/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# The Ore condition for group algebras of lamplighter groups (Kourovka Notebook Problem 12.47)

Kourovka Notebook, Archive of Solved Problems, Problem 12.47 (P. A. Linnell): let `k` be a field,
`p` a prime and `G = ℤₚ ≀ ℤ`. Does `kG` have a classical quotient ring, i.e. do the
non-zero-divisors of `kG` form an Ore set?

We prove that no such group algebra satisfies the right Ore condition. Write `t` for the shift
and `a` for the lamp at zero. Observing a lamp at a fixed offset from the lamplighter kills the
shift difference in `(t - 1)y = (a - 1)x`. The resulting identities give a nonzero left
annihilator of `x` supported on the finite group of configurations on the sites used by `x`.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.47 (P. A.
Linnell). UnsolvedMath record UM-00700866 (`KOU-12.47`), dataset ulamai/UnsolvedMath v1.8.0.

`ℤₚ ≀ ℤ` is the semidirect product of `⨁_{i ∈ ℤ} ℤ/p` (finitely supported functions) by `ℤ` acting
by the shift. Having a classical (right) ring of quotients is the right Ore condition for the
non-zero-divisors, as in Definition 1 of Linnell, Lück and Schick; for group algebras the left and
right conditions are equivalent. The target is stated for some field and some prime (the strongest
true form, existential when refuted, as in WantedExt/Sources/UnsolvedMath.md), so its refutation
asserts that `k[ℤₚ ≀ ℤ]` is not Ore for every field `k` and every prime `p`: stronger than the
source's negative answer, which needs one pair, and what Theorem 3 of Linnell, Lück and Schick
proves.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.LamplighterGroupAlgebraOreKourovka12Problem47Wanted

/-- **Shift of the lamplighter base group.** For a natural number $p$, the shift is the
automorphism $f \mapsto f(\cdot - 1)$ of the base group $\bigoplus_{i \in \mathbb{Z}} \mathbb{Z}/p$,
the additive group of finitely supported functions $\mathbb{Z} \to \mathbb{Z}/p$, viewed as a
multiplicative group. -/
noncomputable def shift (p : ℕ) : MulAut (Multiplicative (ℤ →₀ ZMod p)) :=
  AddEquiv.toMultiplicative (Finsupp.domCongr (Equiv.addRight (1 : ℤ)))

/-- **Lamplighter group.** For a natural number $p$, the lamplighter group
$\mathbb{Z}/p \wr \mathbb{Z}$ is the semidirect product
$\left(\bigoplus_{i \in \mathbb{Z}} \mathbb{Z}/p\right) \rtimes \mathbb{Z}$, in which
$n \in \mathbb{Z}$ acts on the base group by the $n$-th power of the shift
$f \mapsto f(\cdot - 1)$. -/
abbrev Lamplighter (p : ℕ) : Type :=
  Multiplicative (ℤ →₀ ZMod p) ⋊[zpowersHom (MulAut (Multiplicative (ℤ →₀ ZMod p))) (shift p)]
    Multiplicative ℤ

/-- **Non-zero-divisor.** An element $s$ of a ring $R$ is a non-zero-divisor when it is neither a
left nor a right zero divisor: for every $z \in R$, $zs = 0$ implies $z = 0$ and $sz = 0$ implies
$z = 0$. -/
def IsNonZeroDivisor {R : Type*} [Ring R] (s : R) : Prop :=
  (∀ z : R, z * s = 0 → z = 0) ∧ ∀ z : R, s * z = 0 → z = 0

/-- **Right Ore ring.** A ring $R$ satisfies the right Ore condition for its non-zero-divisors, so
that it has a classical right ring of quotients, when for all $s, t \in R$ with $s$ a
non-zero-divisor there are $x, y \in R$ with $x$ a non-zero-divisor and $sy = tx$.

For group algebras the left and right conditions agree. -/
def IsOreRing (R : Type*) [Ring R] : Prop :=
  ∀ s t : R, IsNonZeroDivisor s → ∃ x y : R, IsNonZeroDivisor x ∧ s * y = t * x

/-- **Kourovka Problem 12.47: some lamplighter group algebra is Ore.** There are a field $k$ and a
prime $p$ such that the group algebra $k[\mathbb{Z}/p \wr \mathbb{Z}]$ of the lamplighter group
$\mathbb{Z}/p \wr \mathbb{Z}$ satisfies the right Ore condition for its non-zero-divisors, that
is, has a classical right ring of quotients.

Kourovka 12.47 (P. A. Linnell) asks this for a given field and prime; the existential form makes
its refutation cover every field and every prime. -/
def lamplighterGroupAlgebraOre : Prop :=
  ∃ (k : Type) (_ : Field k) (p : ℕ), p.Prime ∧ IsOreRing (MonoidAlgebra k (Lamplighter p))

noncomputable section

open MonoidAlgebra Multiplicative

private abbrev step (p : ℕ) : Lamplighter p := SemidirectProduct.inr (ofAdd 1)

private abbrev lamp (p : ℕ) : Lamplighter p :=
  SemidirectProduct.inl (ofAdd (Finsupp.single 0 1))

variable {k : Type} [Field k] {p : ℕ}

-- A nonzero element has a highest occupied level, and translating it one step raises that level.
private theorem eq_zero_of_raise (x : k[Lamplighter p]) (f : Lamplighter p → Lamplighter p)
    (hf : ∀ g, (f g).right.toAdd = g.right.toAdd + 1)
    (hx : ∀ g, x.coeff (f g) = x.coeff g) : x = 0 := by
  classical
  by_contra hn
  have hs : x.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr (by simpa using hn)
  obtain ⟨g, hg, hmax⟩ := Finset.exists_max_image x.coeff.support (fun g ↦ g.right.toAdd) hs
  have hfg : f g ∈ x.coeff.support := by simpa only [Finsupp.mem_support_iff, hx] using hg
  have := hmax (f g) hfg
  rw [hf] at this
  omega

private theorem step_regular : IsNonZeroDivisor (single (step p) (1 : k) - 1) := by
  constructor
  · intro x hx
    rw [mul_sub, mul_one, sub_eq_zero] at hx
    apply eq_zero_of_raise x (· * step p) (fun _ ↦ rfl)
    intro g
    simpa using (congrArg (fun z : k[Lamplighter p] ↦ z.coeff (g * step p)) hx).symm
  · intro x hx
    rw [sub_mul, one_mul, sub_eq_zero] at hx
    apply eq_zero_of_raise x (step p * ·) (fun g ↦ add_comm 1 g.right.toAdd)
    intro g
    simpa using (congrArg (fun z : k[Lamplighter p] ↦ z.coeff (step p * g)) hx).symm

-- Observe one lamp at an offset from the current position. This observation is shift-invariant.
private def observe (i : ℤ) (g : Lamplighter p) : ZMod p :=
  g.left.toAdd (g.right.toAdd - i)

private theorem observe_step (i : ℤ) (g : Lamplighter p) :
    observe i (step p * g) = observe i g := by
  unfold observe
  rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right]
  simp only [step, SemidirectProduct.left_inr, one_mul, SemidirectProduct.right_inr,
    zpowersHom_apply, toAdd_ofAdd, zpow_one, toAdd_mul]
  change g.left.toAdd ((1 + g.right.toAdd - i) - 1) = _
  congr 1
  omega

private theorem observe_lamp (i : ℤ) (g : Lamplighter p) :
    observe i (lamp p * g) = (if g.right.toAdd = i then 1 else 0) + observe i g := by
  classical
  simp [observe, lamp, Finsupp.single_apply, eq_comm (a := (0 : ℤ)), sub_eq_zero]

-- Evaluate a linear observation on a left translate, by translating the observation instead.
private theorem eval_translate (b : Lamplighter p) (w : Lamplighter p → k)
    (x : k[Lamplighter p]) :
    Finsupp.linearCombination k w ((single b 1 - 1) * x).coeff =
      Finsupp.linearCombination k (fun g ↦ w (b * g) - w g) x.coeff := by
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy => simp [mul_add, hx, hy]
  | single g r => simp [sub_mul, mul_sub]

private theorem observation_sum (x y : k[Lamplighter p])
    (h : (single (step p) 1 - 1) * y = (single (lamp p) 1 - 1) * x)
    (i : ℤ) (w : ZMod p → k) :
    x.coeff.sum (fun g r ↦ r * (w (observe i (lamp p * g)) - w (observe i g))) = 0 := by
  have he := congrArg (fun z : k[Lamplighter p] ↦
    Finsupp.linearCombination k (fun g ↦ w (observe i g)) z.coeff) h
  rw [eval_translate, eval_translate] at he
  simpa [observe_step, Finsupp.linearCombination_apply] using he.symm

-- At equal heights, the quotient of two group elements just subtracts their lamp configurations.
private theorem left_div_of_right_eq {g u : Lamplighter p} (h : g.right = u.right) :
    (g * u⁻¹).left.toAdd = g.left.toAdd - u.left.toAdd := by
  simp [SemidirectProduct.mul_left, SemidirectProduct.inv_left, h, sub_eq_add_neg]

private abbrev configurations (p : ℕ) (D : Finset ℤ) :=
  Finsupp.supported (ZMod p) ℤ (D : Set ℤ)

-- The signed difference between the two classes of configurations with lamp zero equal to 1 or 0.
private def lampDifference (v : ZMod p) : k :=
  (if v = 1 then 1 else 0) - (if v = 0 then 1 else 0)

-- Restrict this difference to configurations supported on the finite window D at height zero.
private def annihilator [NeZero p] (D : Finset ℤ) : k[Lamplighter p] := by
  classical
  let C := configurations p D
  have : Finite C := Finite.of_equiv _ (Finsupp.supportedEquivFinsupp (R := ℤ)
    (M := ZMod p) (D : Set ℤ)).symm.toEquiv
  let f (g : Lamplighter p) : k :=
    if g.right = 1 ∧ g.left.toAdd ∈ C then lampDifference (g.left.toAdd 0) else 0
  refine ofCoeff (Finsupp.ofSupportFinite f ?_)
  let embed (c : C) : Lamplighter p := SemidirectProduct.inl (ofAdd c.val)
  apply (Set.finite_range embed).subset
  intro g hg
  have h : g.right = 1 ∧ g.left.toAdd ∈ C := by
    by_contra hn
    exact hg (by simp [f, hn])
  exact ⟨⟨g.left.toAdd, h.2⟩, SemidirectProduct.ext rfl h.1.symm⟩

open Classical in
private theorem annihilator_coeff [NeZero p] (D : Finset ℤ) (b : Lamplighter p) :
    (annihilator D : k[Lamplighter p]).coeff b =
      if b.right = 1 ∧ b.left.toAdd ∈ configurations p D then lampDifference (b.left.toAdd 0)
      else 0 := rfl

private def matchesLamp (v t : ZMod p) : k := if v = t then 1 else 0

private theorem lampDifference_translate [NeZero p] (D : Finset ℤ) (g u : Lamplighter p)
    (hg : g.left.toAdd ∈ configurations p D) (hu : u.left.toAdd ∈ configurations p D) :
    (annihilator D : k[Lamplighter p]).coeff (g * u⁻¹) =
      matchesLamp (g.left.toAdd 0) (observe g.right.toAdd (lamp p * u)) -
      matchesLamp (g.left.toAdd 0) (observe g.right.toAdd u) := by
  classical
  rw [annihilator_coeff, observe_lamp]
  have hr : (g * u⁻¹).right = 1 ↔ g.right = u.right := mul_inv_eq_one
  by_cases h : g.right = u.right
  · have hi : u.right.toAdd = g.right.toAdd := congrArg toAdd h.symm
    rw [left_div_of_right_eq h, ite_eq_left ⟨hr.mpr h, (configurations p D).sub_mem hg hu⟩,
      ite_eq_left hi]
    simp only [observe, hi, sub_self, Finsupp.sub_apply, lampDifference, matchesLamp,
      sub_eq_iff_eq_add, zero_add]
  · have hi : u.right.toAdd ≠ g.right.toAdd := fun e ↦ h (toAdd.injective e).symm
    rw [ite_eq_right (fun e ↦ h (hr.mp e.1)), ite_eq_right hi, zero_add, sub_self]

private theorem denominator_singular [Fact p.Prime] (x y : k[Lamplighter p])
    (h : (single (step p) 1 - 1) * y = (single (lamp p) 1 - 1) * x) :
    ¬ IsNonZeroDivisor x := by
  classical
  intro hx
  let D := x.coeff.support.biUnion (fun u ↦ u.left.toAdd.support)
  have hu (u) (hu : u ∈ x.coeff.support) : u.left.toAdd ∈ configurations p D :=
    fun _ hi ↦ Finset.mem_biUnion.mpr ⟨u, hu, hi⟩
  let z : k[Lamplighter p] := annihilator D
  -- Inside the window, convolution with z is an observation of the Ore equation.
  -- Outside it every summand vanishes, since the configurations in x are supported in D.
  have hz0 : z * x = 0 := by
    ext g
    rw [coeff_mul_apply_right]
    by_cases hg : g.left.toAdd ∈ configurations p D
    · refine Eq.trans ?_ (observation_sum x y h g.right.toAdd (matchesLamp (g.left.toAdd 0)))
      apply Finset.sum_congr rfl
      intro u hux
      dsimp only [z]
      rw [lampDifference_translate D g u hg (hu u hux), mul_comm]
    · apply Finset.sum_eq_zero
      intro u hux
      have hn : ¬ ((g * u⁻¹).right = 1 ∧ (g * u⁻¹).left.toAdd ∈ configurations p D) := by
        rintro ⟨he, hm⟩
        have he' : g.right = u.right := mul_inv_eq_one.mp he
        rw [left_div_of_right_eq he'] at hm
        exact hg ((configurations p D).sub_mem_iff_left (hu u hux) |>.mp hm)
      simp only [z, annihilator_coeff, ite_eq_right hn, zero_mul]
  have he : z.coeff 1 = 0 := by rw [hx.1 z hz0]; rfl
  simp [z, annihilator_coeff, lampDifference] at he

/--
**Lamplighter group algebras are not Ore.** For every field $k$ and every prime $p$, the group
algebra $k[\mathbb{Z}/p \wr \mathbb{Z}]$ of the lamplighter group $\mathbb{Z}/p \wr \mathbb{Z}$
does not satisfy the right Ore condition for its non-zero-divisors: there are $s$ and $t$ in it,
with $s$ a non-zero-divisor, such that $sy = tx$ holds for no $x$ and $y$ with $x$ a
non-zero-divisor.

Resolved false: Linnell, Lück and Schick (Theorem 3, with W. Dicks's argument) prove that $kG$ is
not an Ore ring for every field $k$ and every group $G$ containing $H \wr \mathbb{Z}$ with
$H \ne 1$ finite, in particular for $G = \mathbb{Z}/p \wr \mathbb{Z}$ and every prime $p$; the
Kourovka Archive answers 12.47 "No, it does not".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.47
(P. A. Linnell); resolution: P. A. Linnell, W. Lück and T. Schick, The Ore condition, affiliated
operators, and the lamplighter group, in: High-dimensional manifold topology (Trieste, 2001), World
Scientific, 2003, 315-321, Theorem 3: kG is not an Ore ring for every field k and every group G
containing H ≀ ℤ with H ≠ 1 finite; Kourovka Archive, Problem 12.47,
http://him-lueck.uni-bonn.de/data/lamplighter.pdf.
-/
public theorem lamplighterGroupAlgebraOre_refuted : ¬ lamplighterGroupAlgebraOre := by
  rintro ⟨k, inst, p, hp, hore⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, y, hx, h⟩ := hore _ (single (lamp p) 1 - 1) step_regular
  exact denominator_singular x y h hx

end

end MathlibExt.GroupTheory.LamplighterGroupAlgebraOreKourovka12Problem47Wanted
