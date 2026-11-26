/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.MinimalGradedResolution
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Abel

/-!
# Invariance of graded Betti numbers

This module proves equality of degree-shift counts in minimal graded free resolutions.

Reference: Eisenbud, *Commutative Algebra with a View Toward Algebraic
Geometry*, Chapter 20, https://doi.org/10.1007/978-1-4612-5350-1.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MinimalGradedResolutionWanted

open MathlibExt.RingTheory.MinimalGradedResolution

private theorem betti_zero_of_ranks_eq_zero {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M))
    (P : MinimalResolution G) (i : ℕ) (j : ℤ) (h : P.ranks i = 0) :
    betti G P i j = 0 := by
  have hCard : Fintype.card (Fin (P.ranks i)) = 0 := by
    simp [h]
  have hUniv : (Finset.univ : Finset (Fin (P.ranks i))) = ∅ := by
    rw [← Finset.card_eq_zero, Finset.card_univ, hCard]
  unfold betti
  rw [hUniv]
  simp

private def freeProjection {k : Type*} [Field k] {n b : ℕ}
    (degrees : Fin b → ℤ) (j : ℤ) :
    (Fin b → PolynomialRing k n) →ₗ[k] (Fin b → PolynomialRing k n) :=
  LinearMap.pi fun a ↦ (MvPolynomial.weightedHomogeneousComponent
    (fun _ : Fin n ↦ (1 : ℤ)) (j - degrees a)).comp (LinearMap.proj a)

private theorem freeProjection_mem {k : Type*} [Field k] {n b : ℕ}
    (degrees : Fin b → ℤ) (j : ℤ) (x : Fin b → PolynomialRing k n) :
    freeProjection degrees j x ∈ freePiece degrees j := by
  intro a
  exact MvPolynomial.weightedHomogeneousComponent_mem _ _ _

private theorem freeProjection_of_mem {k : Type*} [Field k] {n b : ℕ}
    (degrees : Fin b → ℤ) {j : ℤ} {x : Fin b → PolynomialRing k n}
    (hx : x ∈ freePiece degrees j) : freeProjection degrees j x = x := by
  apply funext
  intro a
  exact MvPolynomial.weightedHomogeneousComponent_eq_self (hx a)

private theorem single_mem_freePiece {k : Type*} [Field k] {n b : ℕ}
    (degrees : Fin b → ℤ) (a : Fin b) :
    Pi.single a (1 : PolynomialRing k n) ∈ freePiece degrees (degrees a) := by
  intro c
  by_cases h : a = c
  · subst c
    simp only [Pi.single_eq_same, sub_self]
    exact MvPolynomial.isWeightedHomogeneous_one k _
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    exact (polynomialPiece (degrees a - degrees c)).zero_mem

private theorem single_monomial_mem {k : Type*} [Field k] {n b : ℕ}
    (degrees : Fin b → ℤ) (a : Fin b) (u : Fin n →₀ ℕ) (r : k) :
    Pi.single a (MvPolynomial.monomial u r) ∈
      freePiece degrees (Finsupp.weight (fun _ : Fin n ↦ (1 : ℤ)) u + degrees a) := by
  intro c
  by_cases h : c = a
  · subst c
    simpa [polynomialPiece] using MvPolynomial.isWeightedHomogeneous_monomial
      (fun _ : Fin n ↦ (1 : ℤ)) u r rfl
  · rw [Pi.single_eq_of_ne h]
    exact (polynomialPiece _).zero_mem

private theorem freeProjection_of_mem_ne {k : Type*} [Field k] {n b : ℕ}
    (degrees : Fin b → ℤ) {d : ℤ} {x : Fin b → PolynomialRing k n}
    (hx : x ∈ freePiece degrees d) (j : ℤ) (hj : j ≠ d) :
    freeProjection degrees j x = 0 := by
  apply funext
  intro a
  change MvPolynomial.weightedHomogeneousComponent
    (fun _ : Fin n ↦ (1 : ℤ)) (j - degrees a) (x a) = 0
  exact MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ (hx a)
    (fun h ↦ hj (sub_left_inj.mp h))

private theorem freePiece_isInternal {k : Type*} [Field k] {n b : ℕ}
    (degrees : Fin b → ℤ) :
    DirectSum.IsInternal (freePiece (k := k) (n := n) degrees) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s v hv hz i hi
    have h := congrArg (freeProjection degrees i) hz
    rw [map_sum, map_zero] at h
    have hs : (∑ d ∈ s, freeProjection degrees i (v d)) = v i := by
      rw [Finset.sum_eq_single i]
      · exact freeProjection_of_mem degrees (hv i hi)
      · intro d hd hdi
        exact freeProjection_of_mem_ne degrees (hv d hd) i (Ne.symm hdi)
      · exact fun hni ↦ (hni hi).elim
    exact hs.symm.trans h
  · apply top_unique
    intro x _
    have hs : ∀ a (p : PolynomialRing k n),
        Pi.single a p ∈ ⨆ d, freePiece degrees d := by
      intro a p
      induction p using MvPolynomial.induction_on' with
      | monomial u r =>
        exact (le_iSup (freePiece degrees) _) (single_monomial_mem degrees a u r)
      | add p q hp hq =>
        rw [Pi.single_add]
        exact Submodule.add_mem _ hp hq
    rw [← Finset.univ_sum_single x]
    exact Submodule.sum_mem _ fun a _ ↦ hs a (x a)

private def pieceProjection {k : Type*} [Field k] {N : Type*}
    [AddCommGroup N] [Module k N] (H : ℤ → Submodule k N)
    (hH : DirectSum.IsInternal H) (j : ℤ) : N →ₗ[k] N :=
  (H j).subtype ∘ₗ DirectSum.component k ℤ (fun d ↦ H d) j ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm.toLinearMap

private theorem pieceProjection_of_mem {k : Type*} [Field k] {N : Type*}
    [AddCommGroup N] [Module k N] (H : ℤ → Submodule k N)
    (hH : DirectSum.IsInternal H) {d : ℤ} {x : N} (hx : x ∈ H d) (j : ℤ) :
    pieceProjection H hH j x = if j = d then x else 0 := by
  by_cases h : j = d
  · subst j
    change ↑((LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm x d) =
      if d = d then x else 0
    rw [hH.ofBijective_coeLinearMap_of_mem hx, ite_eq_left rfl]
  · change ↑((LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm x j) =
      if j = d then x else 0
    rw [hH.ofBijective_coeLinearMap_of_mem_ne (Ne.symm h) hx, ite_eq_right h]
    rfl

private theorem single_smul {k : Type*} [Field k] {n b : ℕ}
    (a : Fin b) (p : PolynomialRing k n) :
    Pi.single a p = p • Pi.single a (1 : PolynomialRing k n) := by
  apply funext
  intro c
  by_cases h : c = a <;> simp [h]

private theorem freeProjection_single {k : Type*} [Field k] {n b : ℕ}
    (degrees : Fin b → ℤ) (j : ℤ) (a : Fin b) (p : PolynomialRing k n) :
    freeProjection degrees j (Pi.single a p) =
      Pi.single a (MvPolynomial.weightedHomogeneousComponent
        (fun _ : Fin n ↦ (1 : ℤ)) (j - degrees a) p) := by
  apply funext
  intro c
  by_cases h : c = a <;> simp [freeProjection, h]

private theorem graded_projection_commutes {k : Type*} [Field k] {n b : ℕ} {N : Type*}
    [AddCommGroup N] [Module (PolynomialRing k n) N]
    [Module k N] [IsScalarTower k (PolynomialRing k n) N]
    (degrees : Fin b → ℤ) (H : ℤ → Submodule k N) (hH : DirectSum.IsInternal H)
    (f : (Fin b → PolynomialRing k n) →ₗ[PolynomialRing k n] N)
    (hf : ∀ d, ∀ x ∈ freePiece degrees d, f x ∈ H d) (j : ℤ)
    (x : Fin b → PolynomialRing k n) :
    f (freeProjection degrees j x) = pieceProjection H hH j (f x) := by
  classical
  have hs : ∀ a (p : PolynomialRing k n),
      f (freeProjection degrees j (Pi.single a p)) =
        pieceProjection H hH j (f (Pi.single a p)) := by
    intro a p
    induction p using MvPolynomial.induction_on' with
    | monomial u r =>
      have hm := MvPolynomial.isWeightedHomogeneous_monomial
        (fun _ : Fin n ↦ (1 : ℤ)) u r rfl
      have hv := single_monomial_mem degrees a u r
      rw [freeProjection_single, MvPolynomial.weightedHomogeneousComponent_of_mem hm,
        pieceProjection_of_mem H hH (hf _ _ hv)]
      have he : j - degrees a = Finsupp.weight (fun _ : Fin n ↦ (1 : ℤ)) u ↔
          j = Finsupp.weight (fun _ : Fin n ↦ (1 : ℤ)) u + degrees a := sub_eq_iff_eq_add
      by_cases h : j = Finsupp.weight (fun _ : Fin n ↦ (1 : ℤ)) u + degrees a
      · simp [h]
      · simp [h, mt he.mp h]
    | add p q hp hq =>
      simpa only [Pi.single_add, map_add] using congrArg₂ (· + ·) hp hq
  rw [← Finset.univ_sum_single x, map_sum, map_sum, map_sum, map_sum]
  exact Finset.sum_congr rfl fun a _ ↦ hs a (x a)

private theorem graded_preimage {k : Type*} [Field k] {n b : ℕ} {N : Type*}
    [AddCommGroup N] [Module (PolynomialRing k n) N]
    [Module k N] [IsScalarTower k (PolynomialRing k n) N]
    (degrees : Fin b → ℤ) (H : ℤ → Submodule k N) (hH : DirectSum.IsInternal H)
    (f : (Fin b → PolynomialRing k n) →ₗ[PolynomialRing k n] N)
    (hf : ∀ d, ∀ x ∈ freePiece degrees d, f x ∈ H d)
    (j : ℤ) (y : N) (hy : y ∈ H j) (hyr : y ∈ LinearMap.range f) :
    ∃ x ∈ freePiece degrees j, f x = y := by
  obtain ⟨x, rfl⟩ := hyr
  refine ⟨freeProjection degrees j x, freeProjection_mem degrees j x, ?_⟩
  rw [graded_projection_commutes degrees H hH f hf,
    pieceProjection_of_mem H hH hy, ite_eq_left rfl]

private def linearFromImages {R : Type*} [CommRing R] {b : ℕ} {N : Type*}
    [AddCommGroup N] [Module R N] (v : Fin b → N) : (Fin b → R) →ₗ[R] N :=
  ∑ a, (LinearMap.proj a).smulRight (v a)

private theorem linearFromImages_apply {R : Type*} [CommRing R] {b : ℕ} {N : Type*}
    [AddCommGroup N] [Module R N] (v : Fin b → N) (x : Fin b → R) :
    linearFromImages v x = ∑ a, x a • v a := by
  simp [linearFromImages]

private theorem linearFromImages_graded {k : Type*} [Field k] {n b : ℕ} {N : Type*}
    [AddCommGroup N] [Module (PolynomialRing k n) N]
    [Module k N] [IsScalarTower k (PolynomialRing k n) N]
    (degrees : Fin b → ℤ) (H : ℤ → Submodule k N)
    (hsmul : ∀ a b, ∀ p ∈ polynomialPiece (k := k) (n := n) a,
      ∀ x ∈ H b, p • x ∈ H (a + b))
    (v : Fin b → N) (hv : ∀ a, v a ∈ H (degrees a))
    (j : ℤ) (x : Fin b → PolynomialRing k n) (hx : x ∈ freePiece degrees j) :
    linearFromImages v x ∈ H j := by
  rw [linearFromImages_apply]
  apply Submodule.sum_mem
  intro a _
  simpa using hsmul (j - degrees a) (degrees a) (x a) (hx a) (v a) (hv a)

private theorem freePiece_smul {k : Type*} [Field k] {n b : ℕ}
    (degrees : Fin b → ℤ) (a c : ℤ) (p : PolynomialRing k n)
    (hp : p ∈ polynomialPiece a) (x : Fin b → PolynomialRing k n)
    (hx : x ∈ freePiece degrees c) : p • x ∈ freePiece degrees (a + c) := by
  intro t
  change MvPolynomial.IsWeightedHomogeneous (fun _ : Fin n ↦ (1 : ℤ))
    (p * x t) ((a + c) - degrees t)
  simpa only [add_sub_assoc] using hp.mul (hx t)

private theorem graded_lift {k : Type*} [Field k] {n a b : ℕ} {N : Type*}
    [AddCommGroup N] [Module (PolynomialRing k n) N]
    [Module k N] [IsScalarTower k (PolynomialRing k n) N]
    (sourceDegrees : Fin a → ℤ) (targetDegrees : Fin b → ℤ)
    (H : ℤ → Submodule k N) (hH : DirectSum.IsInternal H)
    (f : (Fin b → PolynomialRing k n) →ₗ[PolynomialRing k n] N)
    (hf : ∀ d, ∀ x ∈ freePiece targetDegrees d, f x ∈ H d)
    (g : (Fin a → PolynomialRing k n) →ₗ[PolynomialRing k n] N)
    (hg : ∀ d, ∀ x ∈ freePiece sourceDegrees d, g x ∈ H d)
    (hr : LinearMap.range g ≤ LinearMap.range f) :
    ∃ l : (Fin a → PolynomialRing k n) →ₗ[PolynomialRing k n]
        (Fin b → PolynomialRing k n),
      (∀ d, ∀ x ∈ freePiece sourceDegrees d, l x ∈ freePiece targetDegrees d) ∧
        f.comp l = g := by
  classical
  have hv : ∀ t : Fin a, ∃ v ∈ freePiece targetDegrees (sourceDegrees t),
      f v = g (Pi.single t 1) := by
    intro t
    apply graded_preimage targetDegrees H hH f hf
    · exact hg _ _ (single_mem_freePiece sourceDegrees t)
    · exact hr ⟨_, rfl⟩
  choose v hv hfv using hv
  refine ⟨linearFromImages v, ?_, ?_⟩
  · exact linearFromImages_graded sourceDegrees (freePiece targetDegrees)
      (freePiece_smul targetDegrees) v hv
  · apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, linearFromImages_apply, map_sum]
    simp_rw [map_smul, hfv, ← map_smul, ← single_smul, ← map_sum, Finset.univ_sum_single]

private def constantVector {k : Type*} [Field k] {n b : ℕ} :
    (Fin b → PolynomialRing k n) →ₗ[k] (Fin b → k) where
  toFun x a := MvPolynomial.constantCoeff (x a)
  map_add' x y := by ext a; exact map_add _ _ _
  map_smul' c x := by ext a; simp [MvPolynomial.constantCoeff_eq]

private def constantLift {k : Type*} [Field k] {n b : ℕ} :
    (Fin b → k) →ₗ[k] (Fin b → PolynomialRing k n) where
  toFun x a := MvPolynomial.C (x a)
  map_add' x y := by
    apply funext
    intro a
    exact map_add MvPolynomial.C (x a) (y a)
  map_smul' c x := by
    apply funext
    intro a
    simp [Algebra.smul_def, MvPolynomial.algebraMap_eq]

private theorem constantVector_lift {k : Type*} [Field k] {n b : ℕ} (x : Fin b → k) :
    constantVector (n := n) (constantLift x) = x := by
  apply funext
  intro a
  exact MvPolynomial.constantCoeff_C (Fin n) (x a)

private theorem constantVector_smul {k : Type*} [Field k] {n b : ℕ}
    (p : PolynomialRing k n) (x : Fin b → PolynomialRing k n) :
    constantVector (p • x) = MvPolynomial.constantCoeff p • constantVector x := by
  apply funext
  intro a
  exact map_mul MvPolynomial.constantCoeff p (x a)

private def reducedMap {k : Type*} [Field k] {n a b : ℕ}
    (f : (Fin a → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin b → PolynomialRing k n)) : (Fin a → k) →ₗ[k] (Fin b → k) :=
  linearFromImages (R := k) fun t ↦ constantVector (f (Pi.single t 1))

private theorem reducedMap_constantVector {k : Type*} [Field k] {n a b : ℕ}
    (f : (Fin a → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin b → PolynomialRing k n)) (x : Fin a → PolynomialRing k n) :
    reducedMap f (constantVector x) = constantVector (f x) := by
  rw [reducedMap, linearFromImages_apply]
  conv_rhs => rw [← Finset.univ_sum_single x, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  conv_rhs => rw [single_smul, map_smul, constantVector_smul]
  rfl

private theorem constantVector_of_mem_irrelevant {k : Type*} [Field k] {n b : ℕ}
    {x : Fin b → PolynomialRing k n}
    (hx : x ∈ irrelevant (k := k) (n := n) •
      (⊤ : Submodule (PolynomialRing k n) (Fin b → PolynomialRing k n))) :
    constantVector x = 0 := by
  have hI : irrelevant (k := k) (n := n) ≤ RingHom.ker MvPolynomial.constantCoeff := by
    rw [irrelevant, Ideal.span_le]
    rintro _ ⟨t, rfl⟩
    exact MvPolynomial.constantCoeff_X k t
  have hle : irrelevant (k := k) (n := n) •
      (⊤ : Submodule (PolynomialRing k n) (Fin b → PolynomialRing k n)) ≤
        Submodule.pi Set.univ (fun _ : Fin b ↦ RingHom.ker MvPolynomial.constantCoeff) := by
    apply Submodule.smul_le.mpr
    intro p hp z _ t _
    change MvPolynomial.constantCoeff (p * z t) = 0
    rw [map_mul, hI hp, zero_mul]
  apply funext
  intro t
  exact hle hx t (Set.mem_univ t)

private def degreeExtend {k : Type*} [Field k] {b : ℕ} (degrees : Fin b → ℤ) (j : ℤ) :
    ({a : Fin b // degrees a = j} → k) →ₗ[k] (Fin b → k) where
  toFun x a := if h : degrees a = j then x ⟨a, h⟩ else 0
  map_add' x y := by ext a; dsimp; split_ifs <;> simp
  map_smul' c x := by ext a; dsimp; split_ifs <;> simp

private def degreeRestrict {k : Type*} [Field k] {b : ℕ} (degrees : Fin b → ℤ) (j : ℤ) :
    (Fin b → k) →ₗ[k] ({a : Fin b // degrees a = j} → k) :=
  LinearMap.pi fun a ↦ LinearMap.proj a.val

private theorem degreeRestrict_extend {k : Type*} [Field k] {b : ℕ}
    (degrees : Fin b → ℤ) (j : ℤ) (x : {a : Fin b // degrees a = j} → k) :
    degreeRestrict degrees j (degreeExtend degrees j x) = x := by
  apply funext
  intro a
  exact dite_eq_left a.prop

private theorem degreeExtend_restrict {k : Type*} [Field k] {b : ℕ}
    (degrees : Fin b → ℤ) (j : ℤ) (x : Fin b → k)
    (hx : ∀ a, degrees a ≠ j → x a = 0) :
    degreeExtend degrees j (degreeRestrict degrees j x) = x := by
  apply funext
  intro a
  by_cases h : degrees a = j
  · exact dite_eq_left h
  · exact (dite_eq_right h).trans (hx a h).symm

private theorem reducedMap_supported {k : Type*} [Field k] {n a b : ℕ}
    (sourceDegrees : Fin a → ℤ) (targetDegrees : Fin b → ℤ)
    (f : (Fin a → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin b → PolynomialRing k n))
    (hf : ∀ d, ∀ z ∈ freePiece sourceDegrees d, f z ∈ freePiece targetDegrees d)
    (j : ℤ) (x : Fin a → k) (hx : ∀ t, sourceDegrees t ≠ j → x t = 0)
    (s : Fin b) (hs : targetDegrees s ≠ j) : reducedMap f x s = 0 := by
  classical
  rw [reducedMap, linearFromImages_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro t _
  by_cases ht : sourceDegrees t = j
  · have hcoeff : MvPolynomial.constantCoeff (f (Pi.single t 1) s) = 0 := by
      apply MvPolynomial.IsWeightedHomogeneous.coeff_eq_zero
        (hf _ _ (single_mem_freePiece sourceDegrees t) s) 0
      intro h
      have he : (0 : ℤ) = j - targetDegrees s := by
        simpa only [map_zero, ht] using h
      exact hs (sub_eq_zero.mp he.symm).symm
    change x t * MvPolynomial.constantCoeff (f (Pi.single t 1) s) = 0
    rw [hcoeff, mul_zero]
  · simp [hx t ht]

private theorem degree_counts_eq {k : Type*} [Field k] {n a b : ℕ}
    (sourceDegrees : Fin a → ℤ) (targetDegrees : Fin b → ℤ)
    (f : (Fin a → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin b → PolynomialRing k n))
    (g : (Fin b → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin a → PolynomialRing k n))
    (hf : ∀ d, ∀ z ∈ freePiece sourceDegrees d, f z ∈ freePiece targetDegrees d)
    (hg : ∀ d, ∀ z ∈ freePiece targetDegrees d, g z ∈ freePiece sourceDegrees d)
    (hgf : ∀ x, reducedMap g (reducedMap f x) = x)
    (hfg : ∀ x, reducedMap f (reducedMap g x) = x) (j : ℤ) :
    (Finset.univ.filter fun t ↦ sourceDegrees t = j).card =
      (Finset.univ.filter fun t ↦ targetDegrees t = j).card := by
  classical
  let u := (degreeRestrict targetDegrees j).comp
    ((reducedMap f).comp (degreeExtend sourceDegrees j))
  let v := (degreeRestrict sourceDegrees j).comp
    ((reducedMap g).comp (degreeExtend targetDegrees j))
  have hu : ∀ x, degreeExtend targetDegrees j (u x) =
      reducedMap f (degreeExtend sourceDegrees j x) := by
    intro x
    apply degreeExtend_restrict
    exact reducedMap_supported sourceDegrees targetDegrees f hf j _
      (fun t ht ↦ dite_eq_right ht)
  have hv : ∀ x, degreeExtend sourceDegrees j (v x) =
      reducedMap g (degreeExtend targetDegrees j x) := by
    intro x
    apply degreeExtend_restrict
    exact reducedMap_supported targetDegrees sourceDegrees g hg j _
      (fun t ht ↦ dite_eq_right ht)
  have hleft : v.comp u = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change degreeRestrict sourceDegrees j (reducedMap g
      (degreeExtend targetDegrees j (u x))) = x
    rw [hu, hgf, degreeRestrict_extend]
  have hright : u.comp v = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change degreeRestrict targetDegrees j (reducedMap f
      (degreeExtend sourceDegrees j (v x))) = x
    rw [hv, hfg, degreeRestrict_extend]
  have hcard := (LinearEquiv.ofLinearMap u v hright hleft).finrank_eq
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_subtype] using hcard

private theorem augmentation_differential {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (P : MinimalResolution G) :
    P.augmentation.comp (P.differential 0) = 0 :=
  LinearMap.range_le_ker_iff.mp P.exact_zero.le

private theorem differential_differential {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (P : MinimalResolution G) (i : ℕ) :
    (P.differential i).comp (P.differential (i + 1)) = 0 :=
  LinearMap.range_le_ker_iff.mp (P.exact_succ i).le

private inductive ComparisonAt {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (P Q : MinimalResolution G) :
    (i : ℕ) → ((Fin (P.ranks i) → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin (Q.ranks i) → PolynomialRing k n)) → Prop
  | zero {f} (graded : ∀ j, ∀ x ∈ freePiece (P.degrees 0) j,
        f x ∈ freePiece (Q.degrees 0) j)
      (comm : Q.augmentation.comp f = P.augmentation) : ComparisonAt G P Q 0 f
  | succ {i fprev f} (prev : ComparisonAt G P Q i fprev)
      (graded : ∀ j, ∀ x ∈ freePiece (P.degrees (i + 1)) j,
        f x ∈ freePiece (Q.degrees (i + 1)) j)
      (comm : (Q.differential i).comp f = fprev.comp (P.differential i)) :
      ComparisonAt G P Q (i + 1) f

private theorem ComparisonAt.graded {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    {G : Grading (k := k) (n := n) (M := M)} {P Q : MinimalResolution G} {i : ℕ}
    {f : (Fin (P.ranks i) → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin (Q.ranks i) → PolynomialRing k n)} (hf : ComparisonAt G P Q i f) :
    ∀ j, ∀ x ∈ freePiece (P.degrees i) j, f x ∈ freePiece (Q.degrees i) j := by
  cases hf with
  | zero graded _ => exact graded
  | succ _ graded _ => exact graded

private theorem comparison_exists {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (P Q : MinimalResolution G) (i : ℕ) :
    ∃ f, ComparisonAt G P Q i f := by
  induction i with
  | zero =>
    have hr : LinearMap.range P.augmentation ≤ LinearMap.range Q.augmentation := by
      rw [LinearMap.range_eq_top.mpr Q.augmentation_surjective]
      exact le_top
    obtain ⟨f, hf, ha⟩ := graded_lift (P.degrees 0) (Q.degrees 0) G.piece G.isInternal
      Q.augmentation Q.augmentation_graded P.augmentation P.augmentation_graded hr
    exact ⟨f, ComparisonAt.zero hf ha⟩
  | succ i ih =>
    obtain ⟨fprev, hprev⟩ := ih
    have hr : LinearMap.range (fprev.comp (P.differential i)) ≤
        LinearMap.range (Q.differential i) := by
      cases hprev with
      | zero _ ha =>
        rw [Q.exact_zero, LinearMap.range_le_ker_iff, ← LinearMap.comp_assoc, ha,
          augmentation_differential G P]
      | succ hp _ hd =>
        rw [Q.exact_succ, LinearMap.range_le_ker_iff, ← LinearMap.comp_assoc, hd,
          LinearMap.comp_assoc, differential_differential G P, LinearMap.comp_zero]
    obtain ⟨f, hf, hd⟩ := graded_lift (P.degrees (i + 1)) (Q.degrees (i + 1))
      (freePiece (Q.degrees i)) (freePiece_isInternal (Q.degrees i))
      (Q.differential i) (Q.differential_graded i) (fprev.comp (P.differential i))
      (fun j x hx ↦ hprev.graded j _ (P.differential_graded i j x hx)) hr
    exact ⟨f, ComparisonAt.succ hprev hf hd⟩

private theorem comparison_id {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M)) (P : MinimalResolution G) (i : ℕ) :
    ComparisonAt G P P i LinearMap.id := by
  induction i with
  | zero => exact ComparisonAt.zero (fun _ _ hx ↦ hx) (LinearMap.comp_id _)
  | succ i ih =>
    exact ComparisonAt.succ ih (fun _ _ hx ↦ hx) (by simp)

private theorem comparison_comp {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    {G : Grading (k := k) (n := n) (M := M)} {P Q S : MinimalResolution G} {i : ℕ}
    {f : (Fin (P.ranks i) → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin (Q.ranks i) → PolynomialRing k n)}
    {g : (Fin (Q.ranks i) → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin (S.ranks i) → PolynomialRing k n)}
    (hf : ComparisonAt G P Q i f) (hg : ComparisonAt G Q S i g) :
    ComparisonAt G P S i (g.comp f) := by
  induction hf generalizing S with
  | zero hf ha =>
    cases hg with
    | zero hg hb =>
      refine ComparisonAt.zero (P := P) (Q := S) ?_ ?_
      · exact fun j x hx ↦ hg j _ (hf j x hx)
      rw [← LinearMap.comp_assoc, hb, ha]
  | succ hp hf ha ih =>
    cases hg with
    | succ hq hg hb =>
      refine ComparisonAt.succ (ih hq) ?_ ?_
      · exact fun j x hx ↦ hg j _ (hf j x hx)
      rw [← LinearMap.comp_assoc, hb, LinearMap.comp_assoc, ha, ← LinearMap.comp_assoc]

private theorem free_lift {R : Type*} [CommRing R] {a : ℕ} {A B : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (g : (Fin a → R) →ₗ[R] B)
    (hr : LinearMap.range g ≤ LinearMap.range f) :
    ∃ l : (Fin a → R) →ₗ[R] A, f.comp l = g := by
  classical
  have hv : ∀ t : Fin a, ∃ v, f v = g (Pi.single t 1) := by
    intro t
    exact hr ⟨_, rfl⟩
  choose v hv using hv
  refine ⟨linearFromImages v, ?_⟩
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, linearFromImages_apply, map_sum]
  simp_rw [map_smul, hv, ← map_smul]
  have hs : (∑ t, x t • Pi.single t (1 : R)) = x := by
    apply funext
    intro t
    simp [Pi.single_apply]
  rw [← map_sum, hs]

private theorem comparison_homotopy {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    {G : Grading (k := k) (n := n) (M := M)} {P Q : MinimalResolution G} {i : ℕ}
    {f g : (Fin (P.ranks i) → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin (Q.ranks i) → PolynomialRing k n)}
    (hf : ComparisonAt G P Q i f) (hg : ComparisonAt G P Q i g) :
    ∃ h : (Fin (P.ranks i) → PolynomialRing k n) →ₗ[PolynomialRing k n]
        (Fin (Q.ranks (i + 1)) → PolynomialRing k n),
      ∃ e : (Fin (P.ranks i) → PolynomialRing k n) →ₗ[PolynomialRing k n]
          (Fin (Q.ranks i) → PolynomialRing k n),
        f - g = (Q.differential i).comp h + e ∧
          e.comp (P.differential i) = 0 ∧
          LinearMap.range e ≤ irrelevant (k := k) (n := n) • ⊤ := by
  induction i with
  | zero =>
    cases hf with
    | zero _ ha =>
      cases hg with
      | zero _ hb =>
        have hr : LinearMap.range (f - g) ≤ LinearMap.range (Q.differential 0) := by
          rw [Q.exact_zero, LinearMap.range_le_ker_iff, LinearMap.comp_sub, ha, hb,
            sub_self]
        obtain ⟨h, hh⟩ := free_lift (Q.differential 0) (f - g) hr
        exact ⟨h, 0, by simpa using hh.symm, by simp, by simp⟩
  | succ i ih =>
    cases hf with
    | @succ _ fprev _ hfprev _ ha =>
      cases hg with
      | @succ _ gprev _ hgprev _ hb =>
        obtain ⟨hprev, eprev, heq, hezero, _⟩ := ih hfprev hgprev
        let r := f - g - hprev.comp (P.differential i)
        have hr : LinearMap.range r ≤ LinearMap.range (Q.differential (i + 1)) := by
          rw [Q.exact_succ i, LinearMap.range_le_ker_iff]
          dsimp [r]
          rw [LinearMap.comp_sub, LinearMap.comp_sub, ha, hb, ← LinearMap.sub_comp,
            heq, LinearMap.add_comp, ← LinearMap.comp_assoc, hezero]
          abel
        obtain ⟨h, hh⟩ := free_lift (Q.differential (i + 1)) r hr
        refine ⟨h, hprev.comp (P.differential i), ?_, ?_, ?_⟩
        · rw [hh]
          dsimp [r]
          abel
        · rw [LinearMap.comp_assoc, differential_differential G P, LinearMap.comp_zero]
        · rintro _ ⟨x, rfl⟩
          exact Submodule.smul_top_le_comap_smul_top (irrelevant (k := k) (n := n))
            hprev (P.minimal i ⟨x, rfl⟩)

private theorem reduced_comparison_eq {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    {G : Grading (k := k) (n := n) (M := M)} {P Q : MinimalResolution G} {i : ℕ}
    {f g : (Fin (P.ranks i) → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin (Q.ranks i) → PolynomialRing k n)}
    (hf : ComparisonAt G P Q i f) (hg : ComparisonAt G P Q i g)
    (x : Fin (P.ranks i) → k) : reducedMap f x = reducedMap g x := by
  obtain ⟨h, e, heq, _, he⟩ := comparison_homotopy hf hg
  have hfx : reducedMap f x = constantVector (f (constantLift x)) := by
    simpa only [constantVector_lift] using reducedMap_constantVector f (constantLift x)
  have hgx : reducedMap g x = constantVector (g (constantLift x)) := by
    simpa only [constantVector_lift] using reducedMap_constantVector g (constantLift x)
  apply sub_eq_zero.mp
  rw [hfx, hgx, ← map_sub]
  change constantVector ((f - g) (constantLift x)) = 0
  rw [heq, LinearMap.add_apply, map_add]
  have hd := constantVector_of_mem_irrelevant
    (Q.minimal i ⟨h (constantLift x), rfl⟩)
  have he0 := constantVector_of_mem_irrelevant (he ⟨constantLift x, rfl⟩)
  rw [LinearMap.comp_apply, hd, he0, add_zero]

private theorem reducedMap_comp {k : Type*} [Field k] {n a b c : ℕ}
    (f : (Fin a → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin b → PolynomialRing k n))
    (g : (Fin b → PolynomialRing k n) →ₗ[PolynomialRing k n]
      (Fin c → PolynomialRing k n)) (x : Fin a → k) :
    reducedMap (g.comp f) x = reducedMap g (reducedMap f x) := by
  have hf : reducedMap f x = constantVector (f (constantLift x)) := by
    simpa only [constantVector_lift] using reducedMap_constantVector f (constantLift x)
  have hgf : reducedMap (g.comp f) x = constantVector (g (f (constantLift x))) := by
    simpa only [constantVector_lift, LinearMap.comp_apply] using
      reducedMap_constantVector (g.comp f) (constantLift x)
  rw [hf, reducedMap_constantVector, hgf]

private theorem reducedMap_id {k : Type*} [Field k] {n a : ℕ} (x : Fin a → k) :
    reducedMap (LinearMap.id (R := PolynomialRing k n)) x = x := by
  simpa only [constantVector_lift, LinearMap.id_apply] using
    reducedMap_constantVector (LinearMap.id (R := PolynomialRing k n)) (constantLift x)

/-- The graded Betti table does not depend on the chosen minimal resolution. -/
theorem betti_eq {k : Type*} [Field k] {n : ℕ} {M : Type*}
    [AddCommGroup M] [Module (PolynomialRing k n) M]
    [Module k M] [IsScalarTower k (PolynomialRing k n) M]
    [Module.Finite (PolynomialRing k n) M]
    (G : Grading (k := k) (n := n) (M := M))
    (P Q : MinimalResolution G) (i : ℕ) (j : ℤ) :
    betti G P i j = betti G Q i j := by
  by_cases hi : n < i
  · rw [betti_zero_of_ranks_eq_zero G P i j (P.length_bound i hi),
      betti_zero_of_ranks_eq_zero G Q i j (Q.length_bound i hi)]
  · obtain ⟨f, hf⟩ := comparison_exists G P Q i
    obtain ⟨g, hg⟩ := comparison_exists G Q P i
    have hgf : ∀ x, reducedMap g (reducedMap f x) = x := by
      intro x
      have h := reduced_comparison_eq (comparison_comp hf hg) (comparison_id G P i) x
      simpa only [reducedMap_comp, reducedMap_id] using h
    have hfg : ∀ x, reducedMap f (reducedMap g x) = x := by
      intro x
      have h := reduced_comparison_eq (comparison_comp hg hf) (comparison_id G Q i) x
      simpa only [reducedMap_comp, reducedMap_id] using h
    exact degree_counts_eq (P.degrees i) (Q.degrees i) f g hf.graded hg.graded hgf hfg j

end WantedExt.AlgebraicGeometry.MinimalGradedResolutionWanted
