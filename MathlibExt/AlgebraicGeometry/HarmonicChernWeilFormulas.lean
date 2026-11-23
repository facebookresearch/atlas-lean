/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HarmonicReconstructionInterfaces
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Actual higher Chern--Weil coefficients of smooth connections

The coefficient of exterior degree 2j is the principal-minor coefficient
of det(1 + i F / (2 pi)). Every matrix curvature entry uses the actual
native connection. The alternating sum fixes the wedge normalization:
division by 2^j accounts for each two-form and division by j! accounts
for all ordered injections indexing the same principal minor.

The resulting real de Rham classes are constructed from actual closed
forms normalized by those coefficients. They are not independently
chosen Chern maps. Their rational Betti comparison is a separate source
interface; this module does not claim that comparison is already supplied.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.HarmonicChernWeilFormulas

open CategoryTheory TopologicalSpace
open KahlerClassGeometry SmoothHarmonicBundleGeometry ManifoldDifferentialForms
open scoped Manifold ContDiff BigOperators

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Coordinates n) M]
  [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M]
  {r : ℕ} (B : SmoothComplexBundle n M r)

def pairFirst {j : ℕ} (m : Fin j) : Fin (2 * j) := ⟨2 * m.val, by omega⟩
def pairSecond {j : ℕ} (m : Fin j) : Fin (2 * j) := ⟨2 * m.val + 1, by omega⟩

/-- A single principal-minor determinant term, retaining every curvature entry and wedge sign. -/
def curvatureMinorValue (C : SmoothConnection B) (j : ℕ) (i : Fin B.count) (x : M)
    (v : Fin (2 * j) → Coordinates n) (f : Fin j ↪ Fin r)
    (τ : Equiv.Perm (Fin j)) (σ : Equiv.Perm (Fin (2 * j))) : ℂ :=
  (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ) *
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) *
      ∏ m : Fin j, curvatureValue B C.value i x
        (v (σ (pairFirst m))) (v (σ (pairSecond m))) (f m) (f (τ m))

/-- The actual degree-j Chern coefficient, including all higher classes. -/
def chernWeilValue (C : SmoothConnection B) (j : ℕ) (i : Fin B.count) (x : M)
    (v : Fin (2 * j) → Coordinates n) : ℂ :=
  (Complex.I / (2 * (Real.pi : ℂ))) ^ j /
    ((2 : ℂ) ^ j * (Nat.factorial j : ℂ)) *
      ∑ f : Fin j ↪ Fin r, ∑ τ : Equiv.Perm (Fin j), ∑ σ : Equiv.Perm (Fin (2 * j)),
        curvatureMinorValue B C j i x v f τ σ

/-- The signed principal-minor sum of a matrix-valued two-argument form `Ω` evaluated on `2j`
vectors: the sum over `j`-element ordered index families `f`, permutations `τ` of the family and
permutations `σ` of the vectors of `sign τ · sign σ · ∏ₘ Ω(v σ(2m), v σ(2m+1))_{f m, f (τ m)}`. -/
def chernWeilSum {V R : Type*} [CommRing R] (r j : ℕ) (Ω : V → V → Matrix (Fin r) (Fin r) R)
    (v : Fin (2 * j) → V) : R :=
  ∑ f : Fin j ↪ Fin r, ∑ τ : Equiv.Perm (Fin j), ∑ σ : Equiv.Perm (Fin (2 * j)),
    (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : R) * (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) *
      ∏ m : Fin j, Ω (v (σ (pairFirst m))) (v (σ (pairSecond m))) (f m) (f (τ m))

/-- The degree-`j` Chern--Weil polynomial `(i/2π)^j / (2^j j!)` times the signed minor sum. -/
def chernWeilPolynomial {V : Type*} (r j : ℕ) (Ω : V → V → Matrix (Fin r) (Fin r) ℂ)
    (v : Fin (2 * j) → V) : ℂ :=
  (Complex.I / (2 * (Real.pi : ℂ))) ^ j / ((2 : ℂ) ^ j * (Nat.factorial j : ℂ)) *
    chernWeilSum r j Ω v

omit [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
/-- The Chern--Weil coefficient is the Chern--Weil polynomial of the curvature at the point. -/
theorem chernWeilValue_eq_chernWeilPolynomial (C : SmoothConnection B) (j : ℕ) (i : Fin B.count)
    (x : M) (v : Fin (2 * j) → Coordinates n) :
    chernWeilValue B C j i x v = chernWeilPolynomial r j (curvatureValue B C.value i x) v :=
  rfl

/-- The signed minor sum commutes with ring homomorphisms applied to the form's entries. -/
theorem map_chernWeilSum {V R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (r j : ℕ)
    (Ω : V → V → Matrix (Fin r) (Fin r) R) (v : Fin (2 * j) → V) :
    φ (chernWeilSum r j Ω v) = chernWeilSum r j (fun a b => (Ω a b).map φ) v := by
  simp [chernWeilSum, map_sum, map_mul, map_prod, map_intCast]

omit [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
/-- A flat actual connection makes every positive-degree principal-minor term zero. -/
theorem curvatureMinorValue_of_flat (C : SmoothConnection B) (hC : IsFlat B C)
    (j : ℕ) (hj : 0 < j) (i : Fin B.count) (x : M) (hx : x ∈ B.core.baseSet i)
    (v : Fin (2 * j) → Coordinates n) (f : Fin j ↪ Fin r)
    (τ : Equiv.Perm (Fin j)) (σ : Equiv.Perm (Fin (2 * j))) :
    curvatureMinorValue B C j i x v f τ σ = 0 := by
  have hp : (∏ m : Fin j, curvatureValue B C.value i x
      (v (σ (pairFirst m))) (v (σ (pairSecond m))) (f m) (f (τ m))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (⟨0, hj⟩ : Fin j))
    rw [hC i x hx]
    rfl
  simp only [curvatureMinorValue, hp, mul_zero]

omit [IsManifold 𝓘(ℝ, Coordinates n) ∞ M] [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
/-- Flatness annihilates every actual positive Chern--Weil coefficient. -/
theorem chernWeilValue_of_flat (C : SmoothConnection B) (hC : IsFlat B C)
    (j : ℕ) (hj : 0 < j) (i : Fin B.count) (x : M) (hx : x ∈ B.core.baseSet i)
    (v : Fin (2 * j) → Coordinates n) : chernWeilValue B C j i x v = 0 := by
  simp only [chernWeilValue, curvatureMinorValue_of_flat B C hC j hj i x hx,
    Finset.sum_const_zero, mul_zero]

/-- The native de Rham carrier in the actual even degree 2(q+1). -/
abbrev EvenDeRham (q : ℕ) [ExteriorTheory ℝ (Coordinates n) M] :=
  closedForms ℝ (Coordinates n) M ((2 * q + 1) + 1) ⧸
    LinearMap.range (dToClosed ℝ (Coordinates n) M (2 * q + 1))

/-- Input transport is only the literal arithmetic equality of the two degree expressions. -/
def evenVectors (q : ℕ) (v : Fin ((2 * q + 1) + 1) → Coordinates n) :
    Fin (2 * (q + 1)) → Coordinates n :=
  fun m => v (Fin.cast (by omega) m)

/-- An actual closed real Chern--Weil form, fixed in every native smooth frame. -/
structure ChernWeilFormSource [ExteriorTheory ℝ (Coordinates n) M]
    (C : SmoothConnection B) (q : ℕ) where
  form : closedForms ℝ (Coordinates n) M ((2 * q + 1) + 1)
  normalized : ∀ (i : Fin B.count) (x : M), x ∈ B.core.baseSet i →
    ∀ v : Fin ((2 * q + 1) + 1) → Coordinates n,
      form.val.val ⟨x, by trivial⟩ v =
        (chernWeilValue B C (q + 1) i x (evenVectors q v)).re

/-- The class is the actual closed/exact quotient of this normalized form. -/
def chernWeilClass [ExteriorTheory ℝ (Coordinates n) M] {C : SmoothConnection B} {q : ℕ}
    (S : ChernWeilFormSource B C q) : EvenDeRham (n := n) (M := M) q :=
  (LinearMap.range (dToClosed ℝ (Coordinates n) M (2 * q + 1))).mkQ S.form

/-- All positive Chern--Weil classes vanish; no first-class-only substitute is used. -/
def AllPositiveDeRhamChernZero [ExteriorTheory ℝ (Coordinates n) M] (C : SmoothConnection B)
    (S : ∀ q : ℕ, ChernWeilFormSource B C q) : Prop :=
  ∀ q : ℕ, chernWeilClass B (S q) = 0

omit [IsManifold 𝓘(ℂ, Coordinates n) ∞ M] in
/-- Every normalized positive class of an actual flat connection vanishes in the native closed/exact quotient. -/
theorem allPositiveDeRhamChernZero_of_flat [ExteriorTheory ℝ (Coordinates n) M]
    (C : SmoothConnection B) (hC : IsFlat B C) (S : ∀ q : ℕ, ChernWeilFormSource B C q) :
    AllPositiveDeRhamChernZero B C S := by
  intro q
  have hz : (S q).form = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    have he := (S q).normalized (B.core.indexAt x.val) x.val (B.core.mem_baseSet_at x.val) v
    rw [chernWeilValue_of_flat B C hC (q + 1) (Nat.succ_pos q)
      (B.core.indexAt x.val) x.val (B.core.mem_baseSet_at x.val)] at he
    simpa using he
  simp only [chernWeilClass, hz, map_zero]

end MathlibExt.AlgebraicGeometry.HarmonicChernWeilFormulas
