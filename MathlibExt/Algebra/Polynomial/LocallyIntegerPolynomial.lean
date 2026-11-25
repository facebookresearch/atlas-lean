/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.Interval

/-!
# Locally integer polynomial functions

A function on a set of integers is locally integer polynomial if it agrees with an integer
polynomial on every finite subset. Such a function vanishes everywhere if it has infinitely
many zeros.
-/

open Polynomial

namespace MetaMathlibExt

@[expose] public section

/-- **The ring $\mathrm{LIP}(U)$ of locally integer polynomial functions.** For
$U \subseteq \mathbb{Z}$, $\mathrm{LIP}(U)$ is the subring of the ring of all functions
$U \to \mathbb{Z}$ (with pointwise operations) consisting of the functions $f$ such that for
every finite subset $X \subseteq U$ there is a polynomial $p \in \mathbb{Z}[x]$ with $p(x) = f(x)$
for all $x \in X$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Definitions 1 and 2. -/
public def lipSubring (U : Set ℤ) : Subring (U → ℤ) where
  carrier := {f | ∀ X : Finset U, ∃ p : ℤ[X], ∀ x ∈ X, p.eval (x : ℤ) = f x}
  mul_mem' := by
    intro f g hf hg X
    obtain ⟨p, hp⟩ := hf X
    obtain ⟨q, hq⟩ := hg X
    exact ⟨p * q, fun x hx => by simp [hp x hx, hq x hx]⟩
  one_mem' := fun _ => ⟨1, by simp⟩
  add_mem' := by
    intro f g hf hg X
    obtain ⟨p, hp⟩ := hf X
    obtain ⟨q, hq⟩ := hg X
    exact ⟨p + q, fun x hx => by simp [hp x hx, hq x hx]⟩
  zero_mem' := fun _ => ⟨0, by simp⟩
  neg_mem' := by
    intro f hf X
    obtain ⟨p, hp⟩ := hf X
    exact ⟨-p, fun x hx => by simp [hp x hx]⟩

/-- **Membership in $\mathrm{LIP}(U)$.** For $U \subseteq \mathbb{Z}$ and $f : U \to \mathbb{Z}$,
$f$ lies in $\mathrm{LIP}(U)$ if and only if for every finite subset $X \subseteq U$ there is a
polynomial $p \in \mathbb{Z}[x]$ with $p(x) = f(x)$ for all $x \in X$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Definition 1. -/
public theorem mem_lipSubring_iff {U : Set ℤ} {f : U → ℤ} :
    f ∈ lipSubring U ↔ ∀ X : Finset U, ∃ p : ℤ[X], ∀ x ∈ X, p.eval (x : ℤ) = f x :=
  Iff.rfl

/-- **The triangular-number function is not LIP on the integers.** The function
$x \mapsto x(x+1)/2$ on $\mathbb{Z}$ (an integer, since $x(x+1)$ is even) does not belong to
$\mathrm{LIP}(\mathbb{Z})$: no integer polynomial $p$ takes the values $0, 0, 1$ at $-1, 0, 1$,
since $1 - (-1)$ must divide $p(1) - p(-1)$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Section 1 and Example 2. -/
public theorem triangular_not_mem_lipSubring_univ :
    (fun x : (Set.univ : Set ℤ) => (x : ℤ) * ((x : ℤ) + 1) / 2) ∉ lipSubring Set.univ := by
  intro h
  obtain ⟨p, hp⟩ := h {⟨-1, trivial⟩, ⟨1, trivial⟩}
  have h1 := hp ⟨1, trivial⟩ (by simp)
  have h2 := hp ⟨-1, trivial⟩ (by simp)
  have hd := Polynomial.sub_dvd_eval_sub (1 : ℤ) (-1) p
  simp only at h1 h2
  rw [h1, h2] at hd
  norm_num at hd

/-- **The evaluation map from $\mathbb{Z}[x]$ to $\mathrm{LIP}(U)$.** For $U \subseteq \mathbb{Z}$,
the evaluation map is the ring homomorphism from $\mathbb{Z}[x]$ to the ring $\mathrm{LIP}(U)$ of
locally integer polynomial functions on $U$ that sends each integer polynomial $p$ to the function
$U \to \mathbb{Z}$, $u \mapsto p(u)$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 1. -/
public noncomputable def polynomialToLIP (U : Set ℤ) : ℤ[X] →+* lipSubring U :=
  (RingHom.pi fun u : U => Polynomial.evalRingHom (u : ℤ)).codRestrict (lipSubring U)
    fun p _ => ⟨p, fun _ _ => rfl⟩

/-- **Values of the evaluation map into LIP(U).** For $U \subseteq \mathbb{Z}$, an integer
polynomial $p \in \mathbb{Z}[x]$ and $u \in U$, the image of $p$ under the evaluation map
$\mathbb{Z}[x] \to \mathrm{LIP}(U)$ takes the value $p(u)$ at $u$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 1. -/
@[simp] public theorem polynomialToLIP_apply (U : Set ℤ) (p : ℤ[X]) (u : U) :
    (polynomialToLIP U p : U → ℤ) u = p.eval (u : ℤ) :=
  rfl

/-- **Interpolation polynomial.** Let $X \subseteq \mathbb{Z}$ be finite and
$f : \mathbb{Z} \to \mathbb{Z}$. The interpolation polynomial $f_X \in \mathbb{Q}[x]$ of $f$ on $X$
is the Lagrange interpolation polynomial: the unique polynomial with rational coefficients of
degree less than $|X|$ such that $f_X(x) = f(x)$ for every $x \in X$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Section 1 and Definition 3. -/
public noncomputable def interpolationPoly (X : Finset ℤ) (f : ℤ → ℤ) : ℚ[X] :=
  Lagrange.interpolate X (fun z : ℤ => (z : ℚ)) fun z => (f z : ℚ)

/-- **The interpolation polynomial agrees with the function on its nodes.** Let
$X \subseteq \mathbb{Z}$ be finite and $f : \mathbb{Z} \to \mathbb{Z}$. The interpolation polynomial
$f_X \in \mathbb{Q}[x]$ of $f$ on $X$ satisfies $f_X(x) = f(x)$ for every $x \in X$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Section 1. -/
public theorem eval_interpolationPoly {X : Finset ℤ} (f : ℤ → ℤ) {x : ℤ} (hx : x ∈ X) :
    (interpolationPoly X f).eval (x : ℚ) = f x :=
  Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => Int.cast_injective h) hx

/-- **Degree bound for the interpolation polynomial.** Let $X \subseteq \mathbb{Z}$ be finite and
$f : \mathbb{Z} \to \mathbb{Z}$. The interpolation polynomial $f_X \in \mathbb{Q}[x]$ of $f$ on $X$
has degree less than $|X|$, where the zero polynomial has degree $-\infty$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Section 1. -/
public theorem degree_interpolationPoly_lt (X : Finset ℤ) (f : ℤ → ℤ) :
    (interpolationPoly X f).degree < X.card :=
  Lagrange.degree_interpolate_lt _ fun _ _ _ _ h => Int.cast_injective h

/-- **A locally integer polynomial function with infinitely many zeros is zero.** Let
$U \subseteq \mathbb{Z}$ and let $f : U \to \mathbb{Z}$ lie in the ring $\mathrm{LIP}(U)$ of
locally integer polynomial functions on $U$. If $f(x) = 0$ for infinitely many $x \in U$, then
$f(x) = 0$ for every $x \in U$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 3 (`integers-2025-A41-lem-3`). -/
public theorem lip_eq_zero_of_infinite_zeros {U : Set ℤ} {f : U → ℤ}
    (hf : f ∈ lipSubring U) (h : {x : U | f x = 0}.Infinite) : f = 0 := by
  funext m
  have hfin := (Set.finite_Icc ((m : ℤ) - |f m|) (m + |f m|)).preimage
    (Subtype.val_injective (p := (· ∈ U))).injOn
  obtain ⟨x, hx, hfar⟩ := h.exists_notMem_finite hfin
  change f x = 0 at hx
  change ¬ ((m : ℤ) - |f m| ≤ x ∧ (x : ℤ) ≤ m + |f m|) at hfar
  obtain ⟨p, hp⟩ := mem_lipSubring_iff.mp hf {m, x}
  have hdvd := Polynomial.sub_dvd_eval_sub (m : ℤ) x p
  rw [hp m (by simp), hp x (by simp), hx, sub_zero] at hdvd
  apply Int.eq_zero_of_abs_lt_dvd ((abs_dvd _ _).mpr hdvd)
  rw [lt_abs]
  omega

/-- **Locally integer polynomial functions on an infinite set form a domain.** For every infinite
$U \subseteq \mathbb{Z}$, the ring $\mathrm{LIP}(U)$ of locally integer polynomial functions
$U \to \mathbb{Z}$ is an integral domain.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Lemma 4 (`integers-2025-A41-lem-4`). -/
public theorem lipSubring_isDomain {U : Set ℤ} (hU : U.Infinite) :
    IsDomain (lipSubring U) := by
  have := hU.to_subtype
  refine (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨⟨?_⟩, inferInstance⟩
  intro f g hfg
  have hcover : (Set.univ : Set U) ⊆ {x | f.val x = 0} ∪ {x | g.val x = 0} := by
    intro x _
    exact mul_eq_zero.mp (congrArg (fun h : lipSubring U => h.val x) hfg)
  obtain hf | hg := Set.infinite_union.mp (Set.infinite_univ.mono hcover)
  · exact Or.inl (Subtype.ext (lip_eq_zero_of_infinite_zeros f.property hf))
  · exact Or.inr (Subtype.ext (lip_eq_zero_of_infinite_zeros g.property hg))

/-- **$\mathrm{LIP}(\mathbb{Z})$ is closed under the discrete derivative.** If $f$ lies in
$\mathrm{LIP}(\mathbb{Z})$, the ring of locally integer polynomial functions
$\mathbb{Z} \to \mathbb{Z}$, then so does the function $x \mapsto f(x) - f(x - 1)$.

Source: Alexander Borisov, *Locally Integer Polynomial Functions*, INTEGERS 25 (2025),
Article A41, Theorem 5 (`integers-2025-A41-thm-5`). -/
public theorem lip_univ_sub_shift {f : ↥(Set.univ : Set ℤ) → ℤ}
    (hf : f ∈ lipSubring Set.univ) :
    (fun x => f x - f ⟨(x : ℤ) - 1, Set.mem_univ _⟩) ∈ lipSubring Set.univ := by
  rw [mem_lipSubring_iff]
  intro S
  let shift (x : (Set.univ : Set ℤ)) : (Set.univ : Set ℤ) :=
    ⟨(x : ℤ) - 1, Set.mem_univ _⟩
  obtain ⟨p, hp⟩ := mem_lipSubring_iff.mp hf (S ∪ S.image shift)
  refine ⟨p - p.comp (X - C 1), ?_⟩
  intro x hx
  have hshift : shift x ∈ S ∪ S.image shift :=
    Finset.mem_union_right _ (Finset.mem_image_of_mem shift hx)
  rw [eval_sub, eval_comp, eval_sub, eval_X, eval_C, hp x (Finset.mem_union_left _ hx)]
  exact congrArg (f x - ·) (hp (shift x) hshift)

end

end MetaMathlibExt
