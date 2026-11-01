/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Polynomial.Basic

import Mathlib.Analysis.Complex.Order

@[expose] public section

open scoped ComplexOrder

namespace Polynomial
/-- **Real-rooted polynomials.** A complex polynomial $p$ is real-rooted if every element $z$
of its multiset of roots is real, that is, $\operatorname{Im} z = 0$. -/
public def IsRealRooted (p : Polynomial ℂ) : Prop :=
  ∀ z ∈ p.roots, z.im = 0

/-- **Conjugation-invariant polynomials with roots in the closed lower half-plane are real-rooted.**
Let $p$ be a nonzero complex polynomial that is unchanged when complex conjugation is applied to
each of its coefficients. If every root $z$ of $p$ satisfies $\operatorname{Im} z \le 0$, then
$p$ is real-rooted. -/
public theorem isRealRooted_of_map_star_eq_self_of_roots_im_nonpos
    (p : Polynomial ℂ) (hp0 : p ≠ 0)
    (hreal : Polynomial.map (starRingEnd ℂ) p = p)
    (hupper : ∀ z ∈ p.roots, z.im ≤ 0) : p.IsRealRooted := by
  intro z hz
  have hzroot : p.eval z = 0 := (Polynomial.mem_roots hp0).mp hz
  have hconj_eval : p.eval (star z) = 0 := by
    have hmap := Polynomial.eval_map_apply (p := p) (starRingEnd ℂ) z
    rw [hreal, hzroot] at hmap
    simpa using hmap
  have hconj : star z ∈ p.roots := (Polynomial.mem_roots hp0).mpr hconj_eval
  have hzle := hupper z hz
  have hconjle := hupper (star z) hconj
  have hstarim : (star z).im = -z.im := by rfl
  rw [hstarim] at hconjle
  linarith

/-- **Largest real part of a root.** For a complex polynomial $p$, let $\rho(p)$ be the largest
real part $\operatorname{Re} z$ of an element $z$ of the multiset of roots of $p$, with
$\rho(p) = 0$ when that multiset is empty (as it is for nonzero constants and for $p = 0$). -/
public noncomputable def maxRealRoot (p : Polynomial ℂ) : ℝ :=
  if h : (p.roots.map Complex.re).toFinset.Nonempty then
    (p.roots.map Complex.re).toFinset.max' h
  else 0

/-- **Real parts of roots are bounded by the largest one.** Let $p$ be a complex polynomial and
let $\rho(p)$ be the largest real part of an element of its multiset of roots, or $0$ if that
multiset is empty. Then every element $z$ of the multiset of roots of $p$ satisfies
$\operatorname{Re} z \le \rho(p)$. -/
public theorem root_re_le_maxRealRoot {p : Polynomial ℂ} {z : ℂ} (hz : z ∈ p.roots) :
    z.re ≤ p.maxRealRoot := by
  classical
  rw [maxRealRoot]
  split_ifs with h
  · apply Finset.le_max'
    simpa using Multiset.mem_map.mpr ⟨z, hz, rfl⟩
  · exfalso
    apply h
    exact ⟨z.re, by simpa using Multiset.mem_map.mpr ⟨z, hz, rfl⟩⟩

/-- **The largest real part of a root is attained.** Let $p$ be a complex polynomial whose
multiset of roots is nonempty, and let $\rho(p)$ be the largest real part of a root of $p$.
Then some root $z$ of $p$ satisfies $\operatorname{Re} z = \rho(p)$. -/
public theorem exists_root_re_eq_maxRealRoot {p : Polynomial ℂ} (hp : p.roots ≠ 0) :
    ∃ z ∈ p.roots, z.re = p.maxRealRoot := by
  classical
  have hnonempty : (p.roots.map Complex.re).toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty]
    simpa only [ne_eq, Multiset.map_eq_zero] using hp
  rw [maxRealRoot]
  split_ifs with h
  · have hmem := Finset.max'_mem (p.roots.map Complex.re).toFinset h
    rw [Multiset.mem_toFinset] at hmem
    obtain ⟨z, hz, hzeq⟩ := Multiset.mem_map.mp hmem
    exact ⟨z, hz, hzeq⟩
  · exact (h hnonempty).elim

/-- **Nonconstant complex polynomials have a root.** Every complex polynomial of positive
degree has at least one root. -/
public theorem roots_ne_zero_of_natDegree_pos {p : Polynomial ℂ} (hp : 0 < p.natDegree) :
    p.roots ≠ 0 := by
  intro hzero
  have hdegree : p.natDegree = 0 :=
    (IsAlgClosed.roots_eq_zero_iff_natDegree_eq_zero (k := ℂ) (p := p)).mp hzero
  omega

/-- **For a real-rooted polynomial, the largest real part of a root is a root.** Let $p$ be a
real-rooted complex polynomial of positive degree, and let $\rho(p)$ be the largest real part of
a root of $p$. Then the real number $\rho(p)$, viewed as a complex number, is a root of $p$. -/
public theorem coe_maxRealRoot_mem_roots {p : Polynomial ℂ} (hp : p.IsRealRooted)
    (hdegree : 0 < p.natDegree) : (p.maxRealRoot : ℂ) ∈ p.roots := by
  obtain ⟨z, hz, hreal⟩ :=
    exists_root_re_eq_maxRealRoot (roots_ne_zero_of_natDegree_pos hdegree)
  have him : z.im = 0 := hp z hz
  have hzeq : z = (p.maxRealRoot : ℂ) := by
    apply Complex.ext
    · simpa using hreal
    · simpa using him
  rwa [← hzeq]

/-- **Monic real-rooted polynomials have positive real part right of the largest root.**
Let $p$ be a monic real-rooted complex polynomial, and let $\rho(p)$ be the largest real part of
a root of $p$, or $0$ if $p$ has no roots. Then $\operatorname{Re} p(x) > 0$ for every real
number $x > \rho(p)$. -/
public theorem eval_re_pos_of_maxRealRoot_lt {p : Polynomial ℂ} (hmonic : p.Monic)
    (hrooted : p.IsRealRooted) {x : ℝ} (hx : p.maxRealRoot < x) :
    0 < (p.eval (x : ℂ)).re := by
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hmonic]
  have hprod : 0 < (p.roots.map (fun z ↦ (x : ℂ) - z)).prod := by
    apply Multiset.prod_pos
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    rw [RCLike.pos_iff]
    constructor
    · exact sub_pos.mpr (lt_of_le_of_lt (root_re_le_maxRealRoot hz) hx)
    · simpa using hrooted z hz
  exact (RCLike.pos_iff.mp hprod).1

/-- **Monic real-rooted polynomials have nonnegative real part from the largest root on.**
Let $p$ be a monic real-rooted complex polynomial, and let $\rho(p)$ be the largest real part of
a root of $p$, or $0$ if $p$ has no roots. Then $\operatorname{Re} p(x) \ge 0$ for every real
number $x \ge \rho(p)$. -/
public theorem eval_re_nonneg_of_maxRealRoot_le {p : Polynomial ℂ} (hmonic : p.Monic)
    (hrooted : p.IsRealRooted) {x : ℝ} (hx : p.maxRealRoot ≤ x) :
    0 ≤ (p.eval (x : ℂ)).re := by
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots_of_monic hmonic]
  have hprod : 0 ≤ (p.roots.map (fun z ↦ (x : ℂ) - z)).prod := by
    apply Multiset.prod_nonneg
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hw
    rw [RCLike.nonneg_iff]
    constructor
    · exact sub_nonneg.mpr (root_re_le_maxRealRoot hz |>.trans hx)
    · simpa using hrooted z hz
  exact (RCLike.nonneg_iff.mp hprod).1

end Polynomial
