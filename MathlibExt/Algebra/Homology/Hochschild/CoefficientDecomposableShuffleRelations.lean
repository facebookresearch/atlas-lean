/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianShuffle
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricCoefficientMaps

/-!
# Decomposable shuffle relations with coefficients

Regular decomposables are products of two positive chain
degrees. Applying the regular coefficient head to m in M
gives their coefficient tensor images, whose sum is the
proper both-positive relation module. The full ideal action
also allows a degree-zero second factor. Ground, algebra
and coefficient universes remain independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct MonoidalCategory

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The original regular algebra acts on the chosen original coefficient. -/
def regularHeadEvaluation (m : M) : ULift.{w} A →ₗ[k] M :=
  { toFun := fun a => a.down • m
    map_add' := fun a b => add_smul a.down b.down m
    map_smul' := fun r a => smul_assoc r a.down m }

omit [SMulCommClass k A M] in
/-- The original regular-head evaluation retains the scalar action. -/
theorem regularHeadEvaluation_up (m : M) (a : A) :
    regularHeadEvaluation k A M m (ULift.up a) = a • m := rfl

/-- The tensor map evaluates the regular coefficient and fixes all original tails. -/
def regularCoefficientEvaluation (m : M) (n : ℕ) :
    ULift.{w} A ⊗[k] TensorPower k n A →ₗ[k] M ⊗[k] TensorPower k n A :=
  TensorProduct.map (regularHeadEvaluation k A M m) LinearMap.id

omit [SMulCommClass k A M] in
/-- The regular word has the same original tail after coefficient evaluation. -/
theorem regularCoefficientEvaluation_tmul (m : M) (n : ℕ) (a : ULift.{w} A) (t : TensorPower k n A) :
    regularCoefficientEvaluation k A M m n (a ⊗ₜ[k] t) = (a.down • m) ⊗ₜ[k] t := rfl

/-- The decomposable coefficient family is the sum of images of the regular both-positive family. -/
def coefficientDecomposableShuffleRelations (n : ℕ) : Submodule k (M ⊗[k] TensorPower k n A) :=
  ⨆ m : M, (rawPositiveRelations k A (ULift.{w} A) n).map
    (regularCoefficientEvaluation k A M m n)

/-- Native coefficient evaluation intertwines each original shuffle, retaining its signed tail. -/
theorem regularCoefficientEvaluation_pair (m : M) (p q : ℕ)
    (a0 : ULift.{max v w} A) (b0 : ULift.{w} A)
    (x : TensorPower k p A) (y : TensorPower k q A) :
    regularCoefficientEvaluation k A M m (p + q)
      (coefficientShufflePairingMap k A (ULift.{w} A) p q ((a0 ⊗ₜ[k] x) ⊗ₜ[k] (b0 ⊗ₜ[k] y))) =
    coefficientShufflePairingMap k A M p q
      (((ULift.up a0.down : ULift.{w} A) ⊗ₜ[k] x) ⊗ₜ[k] ((b0.down • m) ⊗ₜ[k] y)) := by
  rw [coefficientShufflePairingMap_tmul, regularCoefficientEvaluation_tmul,
    coefficientShufflePairingMap_tmul]
  change ((a0.down * b0.down) • m) ⊗ₜ[k] _ = (a0.down • (b0.down • m)) ⊗ₜ[k] _
  rw [mul_smul]

/-- Every evaluated regular proper product belongs to the original arbitrary-coefficient proper relation family. -/
theorem regularCoefficientEvaluation_mem (m : M) (n : ℕ)
    {x : ULift.{w} A ⊗[k] TensorPower k n A} (hx : x ∈ rawPositiveRelations k A (ULift.{w} A) n) :
    regularCoefficientEvaluation k A M m n x ∈ rawPositiveRelations k A M n := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  let F := regularCoefficientEvaluation k A M m n
  let S := rawPositiveRelations k A M n
  have hle : rawPositiveRelations k A (ULift.{w} A) n ≤ S.comap F := by
    change HomologicalComplex.ChainGradedPairing.positiveImages
      (pairing.{u, v, max v w} k A (ULift.{w} A)) n ≤ S.comap F
    apply iSup_le
    rintro ⟨⟨p, q⟩, hp, hq, hn⟩
    subst n
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    let P := coefficientShufflePairingMap k A (ULift.{w} A) p q
    let E := regularCoefficientEvaluation k A M m (p + q)
    have hP :
        (HomologicalComplex.ChainGradedPairing.pairAt
          (pairing.{u, v, max v w} k A (ULift.{w} A)) p q (p + q) rfl).hom = P :=
      pairing_pair_eq_coefficientShuffleMap k A (ULift.{w} A) p q
    change E ((HomologicalComplex.ChainGradedPairing.pairAt
      (pairing.{u, v, max v w} k A (ULift.{w} A)) p q (p + q) rfl).hom t) ∈ S
    let t' : (ULift.{max v w} A ⊗[k] TensorPower k p A) ⊗[k]
        (ULift.{w} A ⊗[k] TensorPower k q A) := t
    have hmem : ∀ z : (ULift.{max v w} A ⊗[k] TensorPower k p A) ⊗[k]
        (ULift.{w} A ⊗[k] TensorPower k q A), E (P z) ∈ S := by
      intro z
      refine TensorProduct.inductionOn z ?_ ?_
      · intro a b
        refine TensorProduct.inductionOn a ?_ ?_
        · intro a0 ta
          refine TensorProduct.inductionOn b ?_ ?_
          · intro b0 tb
            have he := regularCoefficientEvaluation_pair k A M m p q a0 b0 ta tb
            have hm := HomologicalComplex.ChainGradedPairing.pairAt_mem_positiveImages
              (pairing.{u, v, w} k A M) p q (p + q) rfl hp hq
                (((ULift.up a0.down : ULift.{w} A) ⊗ₜ[k] ta) ⊗ₜ[k] ((b0.down • m) ⊗ₜ[k] tb))
            have hM := pairing_pair_eq_coefficientShuffleMap k A M p q
            have hm' : coefficientShufflePairingMap k A M p q
                (((ULift.up a0.down : ULift.{w} A) ⊗ₜ[k] ta) ⊗ₜ[k] ((b0.down • m) ⊗ₜ[k] tb)) ∈ S := by
              exact (congrArg (fun f => f
                (((ULift.up a0.down : ULift.{w} A) ⊗ₜ[k] ta) ⊗ₜ[k] ((b0.down • m) ⊗ₜ[k] tb))) hM) ▸ hm
            exact he.symm ▸ hm'
          · intro b c hb hc
            rw [TensorProduct.tmul_add, P.map_add, E.map_add]
            exact S.add_mem hb hc
        · intro a c ha hc
          rw [TensorProduct.add_tmul, P.map_add, E.map_add]
          exact S.add_mem ha hc
      · intro a b ha hb
        rw [P.map_add, E.map_add]
        exact S.add_mem ha hb
    exact (congrArg (fun f => E (f t')) hP).symm ▸ hmem t'
  exact hle hx

/-- The regular-decomposable coefficient family is contained in the original proper relations. -/
theorem coefficientDecomposableShuffleRelations_le (n : ℕ) :
    coefficientDecomposableShuffleRelations k A M n ≤ rawPositiveRelations k A M n := by
  apply iSup_le
  intro m x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact regularCoefficientEvaluation_mem k A M m n hy

/-- Each original coefficient shuffle generator is the evaluation of a regular two-positive-factor product; the regular second head is one. -/
theorem coefficientPair_mem_decomposable (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (a0 : ULift.{w} A) (m : M) (x : TensorPower k p A) (y : TensorPower k q A) :
    coefficientShufflePairingMap k A M p q ((a0 ⊗ₜ[k] x) ⊗ₜ[k] (m ⊗ₜ[k] y)) ∈
      coefficientDecomposableShuffleRelations k A M (p + q) := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  let a0' : ULift.{max v w} A := ULift.up a0.down
  let b0 : ULift.{w} A := ULift.up 1
  let z := coefficientShufflePairingMap k A (ULift.{w} A) p q
    ((a0' ⊗ₜ[k] x) ⊗ₜ[k] (b0 ⊗ₜ[k] y))
  have hz : z ∈ rawPositiveRelations k A (ULift.{w} A) (p + q) := by
    have hm := HomologicalComplex.ChainGradedPairing.pairAt_mem_positiveImages
      (pairing.{u, v, max v w} k A (ULift.{w} A)) p q (p + q) rfl hp hq
        ((a0' ⊗ₜ[k] x) ⊗ₜ[k] (b0 ⊗ₜ[k] y))
    have he := pairing_pair_eq_coefficientShuffleMap k A (ULift.{w} A) p q
    have hm' : coefficientShufflePairingMap k A (ULift.{w} A) p q
        ((a0' ⊗ₜ[k] x) ⊗ₜ[k] (b0 ⊗ₜ[k] y)) ∈
          rawPositiveRelations k A (ULift.{w} A) (p + q) := by
      exact (congrArg (fun f => f ((a0' ⊗ₜ[k] x) ⊗ₜ[k] (b0 ⊗ₜ[k] y))) he) ▸ hm
    exact hm'
  have he : regularCoefficientEvaluation k A M m (p + q) z =
      coefficientShufflePairingMap k A M p q ((a0 ⊗ₜ[k] x) ⊗ₜ[k] (m ⊗ₜ[k] y)) := by
    have h := regularCoefficientEvaluation_pair k A M m p q a0' b0 x y
    have hb : b0.down • m = m := one_smul A m
    exact h.trans (congrArg (fun m' : M => coefficientShufflePairingMap k A M p q
      ((a0 ⊗ₜ[k] x) ⊗ₜ[k] (m' ⊗ₜ[k] y))) hb)
  apply Submodule.mem_iSup_of_mem m
  exact Submodule.mem_map.mpr ⟨z, hz, he⟩

/-- Every original two-positive-factor coefficient relation is an evaluated regular decomposable. -/
theorem rawPositiveRelations_le_coefficientDecomposable (n : ℕ) :
    rawPositiveRelations k A M n ≤ coefficientDecomposableShuffleRelations k A M n := by
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  change HomologicalComplex.ChainGradedPairing.positiveImages (pairing.{u, v, w} k A M) n ≤ _
  apply iSup_le
  rintro ⟨⟨p, q⟩, hp, hq, hn⟩
  subst n
  intro z hz
  obtain ⟨t, rfl⟩ := hz
  let P := coefficientShufflePairingMap k A M p q
  let S := coefficientDecomposableShuffleRelations k A M (p + q)
  have hP : (HomologicalComplex.ChainGradedPairing.pairAt
      (pairing.{u, v, w} k A M) p q (p + q) rfl).hom = P :=
    pairing_pair_eq_coefficientShuffleMap k A M p q
  change (HomologicalComplex.ChainGradedPairing.pairAt
    (pairing.{u, v, w} k A M) p q (p + q) rfl).hom t ∈ S
  let t' : (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (M ⊗[k] TensorPower k q A) := t
  have hmem : ∀ z : (ULift.{w} A ⊗[k] TensorPower k p A) ⊗[k] (M ⊗[k] TensorPower k q A), P z ∈ S := by
    intro z
    refine TensorProduct.inductionOn z ?_ ?_
    · intro a b
      refine TensorProduct.inductionOn a ?_ ?_
      · intro a0 x
        refine TensorProduct.inductionOn b ?_ ?_
        · intro m y
          exact coefficientPair_mem_decomposable k A M p q hp hq a0 m x y
        · intro b c hb hc
          rw [TensorProduct.tmul_add, P.map_add]
          exact S.add_mem hb hc
      · intro a b ha hb
        rw [TensorProduct.add_tmul, P.map_add]
        exact S.add_mem ha hb
    · intro a b ha hb
      rw [P.map_add]
      exact S.add_mem ha hb
  exact (congrArg (fun f => f t') hP).symm ▸ hmem t'

/-- The regular-decomposable coefficient images are exactly the original proper-shuffle relations. -/
theorem coefficientDecomposableShuffleRelations_eq (n : ℕ) :
    coefficientDecomposableShuffleRelations k A M n = rawPositiveRelations k A M n :=
  le_antisymm (coefficientDecomposableShuffleRelations_le k A M n)
    (rawPositiveRelations_le_coefficientDecomposable k A M n)

/-- The native quotient equivalence identifies the original coefficient classes. -/
def coefficientDecomposableShuffleQuotientIso (n : ℕ) :
    ModuleCat.of k ((M ⊗[k] TensorPower k n A) ⧸ coefficientDecomposableShuffleRelations k A M n) ≅
      (positiveQuotient k A M).X n :=
  (Submodule.quotEquivOfEq _ _ (coefficientDecomposableShuffleRelations_eq k A M n)).toModuleIso

/-- The quotient comparison fixes each original coefficient tensor representative. -/
theorem coefficientDecomposableShuffleQuotientIso_mk (n : ℕ) (x : M ⊗[k] TensorPower k n A) :
    (coefficientDecomposableShuffleQuotientIso k A M n).hom.hom
      ((coefficientDecomposableShuffleRelations k A M n).mkQ x) =
        (rawPositiveRelations k A M n).mkQ x :=
  Submodule.quotEquivOfEq_mk _ _ (coefficientDecomposableShuffleRelations_eq k A M n) x

/-- The evaluated regular decomposable family has no degree-zero generators. -/
theorem coefficientDecomposableShuffleRelations_zero :
    coefficientDecomposableShuffleRelations k A M 0 = ⊥ := by
  rw [coefficientDecomposableShuffleRelations_eq]
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.positiveImages_zero (pairing.{u, v, w} k A M)

/-- Degree zero remains the original empty-tail coefficient tensor. -/
def coefficientDecomposableShuffleDegreeZeroIso :
    ModuleCat.of k ((M ⊗[k] TensorPower k 0 A) ⧸ coefficientDecomposableShuffleRelations k A M 0) ≅
      ModuleCat.of k (M ⊗[k] TensorPower k 0 A) :=
  ((coefficientDecomposableShuffleRelations k A M 0).quotEquivOfEqBot
    (coefficientDecomposableShuffleRelations_zero k A M)).toModuleIso

/-- The decomposable quotient complex reuses the original proper quotient engine. -/
abbrev coefficientDecomposableShuffleComplex : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  positiveQuotient k A M

/-- The original representative differential is preserved by the degree quotient comparison. -/
theorem coefficientDecomposableShuffleQuotientIso_boundary (n : ℕ)
    (x : M ⊗[k] TensorPower k (n + 1) A) :
    ((coefficientDecomposableShuffleComplex k A M).d (n + 1) n).hom
      ((coefficientDecomposableShuffleQuotientIso k A M (n + 1)).hom.hom
        ((coefficientDecomposableShuffleRelations k A M (n + 1)).mkQ x)) =
    (coefficientDecomposableShuffleQuotientIso k A M n).hom.hom
      ((coefficientDecomposableShuffleRelations k A M n).mkQ (algebraBoundary k A M n x)) := by
  rw [coefficientDecomposableShuffleQuotientIso_mk, coefficientDecomposableShuffleQuotientIso_mk]
  exact positiveQuotient_d_mk k A M n x

/-- The original Hochschild boundary preserves the evaluated regular decomposables. -/
theorem coefficientDecomposableShuffleRelations_boundary (n : ℕ) :
    coefficientDecomposableShuffleRelations k A M (n + 1) ≤
      (coefficientDecomposableShuffleRelations k A M n).comap
        (((chainComplex k A M).d (n + 1) n).hom) := by
  rw [coefficientDecomposableShuffleRelations_eq, coefficientDecomposableShuffleRelations_eq]
  let _ : MonoidalCategoryStruct (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.tensorStructure.{u, max v w} (R := k)
  let _ : MonoidalCategory (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u, max v w} (R := k)
  let _ : MonoidalPreadditive (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u, max v w} (R := k)
  let _ : MonoidalLinear k (ModuleCat.{max u v w} k) :=
    ModuleCat.UniverseTensor.monoidalLinear.{u, max v w} (R := k)
  exact HomologicalComplex.ChainGradedPairing.positiveImages_d (pairing.{u, v, w} k A M)
    (boundary_one_zero k A (ULift.{w} A)) (boundary_one_zero k A M) n

/-- Coefficient-linear maps preserve the evaluated regular decomposable family,
through the original proper-shuffle coefficient-map law. -/
theorem coefficientDecomposableShuffleRelations_coefficient
    {N : Type w} [AddCommGroup N] [Module k N] [Module A N]
    [SMulCommClass k A N] [IsScalarTower k A N] (f : M →ₗ[A] N) (n : ℕ) :
    coefficientDecomposableShuffleRelations k A M n ≤
      (coefficientDecomposableShuffleRelations k A N n).comap
        ((algebraCoefficientLevelMap k A f n).restrictScalars k) := by
  rw [coefficientDecomposableShuffleRelations_eq, coefficientDecomposableShuffleRelations_eq]
  exact algebraCoefficientLevelMap_positiveRelations k A f n

end ModuleCat.Algebra.Hochschild.Symmetric
