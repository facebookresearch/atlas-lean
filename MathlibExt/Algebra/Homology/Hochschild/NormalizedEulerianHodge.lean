/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.RationalEulerianComplex
public import MathlibExt.Algebra.Homology.Hochschild.NormalizedEulerianOperators
public import MathlibExt.LinearAlgebra.TensorPower.PermutationActionNaturality

/-!
# Rational normalized Hodge decomposition

Over a rational ground algebra, the
normalized coefficient Eulerian chain
projectors are finite, orthogonal and
complete in each degree. Their images
decompose the normalized complex and
homology, naturally under factorwise
normalization without coefficient flatness.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

local instance : Module Aᵐᵒᵖ M := opModule A M
local instance : SMulCommClass A Aᵐᵒᵖ M := actionsComm A M
local instance : SMulCommClass k Aᵐᵒᵖ M := kOpComm k A M
local instance : IsScalarTower k Aᵐᵒᵖ M := kOpTower k A M

/-- The degree-zero projector is the original identity, not a zero positive-degree convention. -/
theorem normalizedEulerianOperator_degree_zero :
    normalizedEulerianOperator k A M 0 0 = LinearMap.id := by
  classical
  letI : Unique (Fin 1) :=
    { default := 0, uniq := fun i => Fin.ext (by have hi := i.isLt; omega) }
  have h : (∑ i : Fin 1, normalizedEulerianOperator k A M 0 i.val) = LinearMap.id :=
    normalizedEulerianOperator_sum k A M 0
  have hval (i : Fin 1) : i.val = 0 := by
    have hi := i.isLt
    omega
  simpa only [Fintype.sum_unique, hval] using h

/-- Positive original degrees have zero weight-zero component. -/
theorem normalizedEulerianOperator_zero_weight (n : ℕ) (hn : 0 < n) :
    normalizedEulerianOperator k A M n 0 = 0 := by
  unfold normalizedEulerianOperator Equiv.Perm.eulerianElement
  simp_rw [Equiv.Perm.eulerianCoefficient_zero_weight n _ hn, MonoidAlgebra.single_zero]
  rw [Finset.sum_const_zero, map_zero]

/-- The native normalized chain projector retains its original coefficient-word component. -/
theorem normalizedEulerianChainMap_f (n i : ℕ) :
    ((normalizedEulerianChainMap k A M i).f n).hom = normalizedEulerianOperator k A M n i := rfl

/-- Native normalized chain composition is the orthogonal projector law. -/
theorem normalizedEulerianChainMap_comp (i j : ℕ) :
    normalizedEulerianChainMap k A M i ≫ normalizedEulerianChainMap k A M j =
      if i = j then normalizedEulerianChainMap k A M i else 0 := by
  by_cases h : i = j
  · rw [if_pos h]
    subst j
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (normalizedEulerianOperator k A M n i).comp (normalizedEulerianOperator k A M n i) =
      normalizedEulerianOperator k A M n i
    exact (normalizedEulerianOperator_comp k A M n i i).trans (if_pos rfl)
  · rw [if_neg h]
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (normalizedEulerianOperator k A M n j).comp (normalizedEulerianOperator k A M n i) = 0
    exact (normalizedEulerianOperator_comp k A M n j i).trans (if_neg (Ne.symm h))

/-- Every normalized component has its original tensor-degree support. -/
theorem normalizedEulerianChainMap_support (n i : ℕ) (h : n < i) :
    (normalizedEulerianChainMap k A M i).f n = 0 := by
  apply ModuleCat.hom_ext
  rw [normalizedEulerianChainMap_f, normalizedEulerianOperator_outside k A M n i h]
  rfl

/-- Native normalized finite completeness gives exactly the original degree identity. -/
theorem normalizedEulerianChainMap_sum (n : ℕ) :
    (∑ i : Fin (n + 1), (normalizedEulerianChainMap k A M i.val).f n) =
      𝟙 ((normalizedChainComplex k A M).X n) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_id, normalizedEulerianChainMap_f]
  change (∑ i : Fin (n + 1), normalizedEulerianOperator k A M n i.val) = LinearMap.id
  exact normalizedEulerianOperator_sum k A M n

/-- The normalized weight complex is the native image of its original chain projector. -/
def normalizedEulerianImageComplex (i : ℕ) : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  image (normalizedEulerianChainMap k A M i)

/-- The sum of normalized image inclusions gives the full native Hodge complex isomorphism. -/
def normalizedHodgeComplexIso :
    (∐ (fun i : ℕ => normalizedEulerianImageComplex k A M i)) ≅ normalizedChainComplex k A M :=
  HomologicalComplex.locallyFiniteIdempotentImageComplexIso
    (normalizedChainComplex k A M) (normalizedEulerianChainMap k A M)
    (normalizedEulerianChainMap_comp k A M) id
    (normalizedEulerianChainMap_support k A M) (normalizedEulerianChainMap_sum k A M)

/-- The original normalized image inclusions are retained as the forward decomposition map. -/
theorem normalizedHodgeComplexIso_hom :
    (normalizedHodgeComplexIso k A M).hom =
      Sigma.desc (fun i => image.ι (normalizedEulerianChainMap k A M i)) := rfl

/-- The normalized image homologies give the native Hodge homology coproduct. -/
def normalizedHodgeHomologyIso (n : ℕ) :
    (∐ (fun i : ℕ => (normalizedEulerianImageComplex k A M i).homology n)) ≅
      (normalizedChainComplex k A M).homology n :=
  HomologicalComplex.locallyFiniteIdempotentImageHomologyIso
    (normalizedChainComplex k A M) (normalizedEulerianChainMap k A M)
    (normalizedEulerianChainMap_comp k A M) id
    (normalizedEulerianChainMap_support k A M) (normalizedEulerianChainMap_sum k A M) n

/-- The original normalized Hodge decomposition map is homology of its native image inclusions. -/
theorem normalizedHodgeHomologyIso_hom (n : ℕ) :
    (normalizedHodgeHomologyIso k A M n).hom = Sigma.desc
      (fun i => HomologicalComplex.homologyMap (image.ι (normalizedEulerianChainMap k A M i)) n) := rfl

/-- The original normalized Hodge homology projector. -/
def normalizedEulerianHomologyProjector (n i : ℕ) :
    (normalizedChainComplex k A M).homology n ⟶ (normalizedChainComplex k A M).homology n :=
  HomologicalComplex.homologyMap (normalizedEulerianChainMap k A M i) n

/-- Its homology projections retain the orthogonal projector law. -/
theorem normalizedEulerianHomologyProjector_comp (n i j : ℕ) :
    normalizedEulerianHomologyProjector k A M n i ≫ normalizedEulerianHomologyProjector k A M n j =
      if i = j then normalizedEulerianHomologyProjector k A M n i else 0 := by
  rw [normalizedEulerianHomologyProjector, normalizedEulerianHomologyProjector,
    ← HomologicalComplex.homologyMap_comp, normalizedEulerianChainMap_comp]
  split_ifs
  · rfl
  · exact HomologicalComplex.homologyMap_zero
      (K := normalizedChainComplex k A M) (L := normalizedChainComplex k A M) (i := n)

/-- The original quotient chain projection intertwines every raw and normalized Eulerian projector. -/
@[reassoc]
theorem normalizationProjection_eulerian (i : ℕ) :
    eulerianChainMap k A M i ≫ normalizationProjection k A M =
      normalizationProjection k A M ≫ normalizedEulerianChainMap k A M i := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, eulerianChainMap_f,
    normalizedEulerianChainMap_f]
  have hP : ((normalizationProjection k A M).f n).hom =
      TensorPower.coefficientQuotientMap (ModuleCat.Algebra.Hochschild.unitSubmodule k A) M n := by
    change ((ModuleCat.Algebra.Hochschild.normalizationProjection k A M).f n).hom = _
    rw [ModuleCat.Algebra.Hochschild.normalizationProjection_f]
    rfl
  rw [hP]
  exact TensorPower.coefficientRationalPermutationAction_naturality n
    (Equiv.Perm.eulerianElement n i) (ModuleCat.Algebra.Hochschild.unitSubmodule k A).mkQ LinearMap.id

/-- Native homology of the quotient map preserves the original Hodge weights. -/
@[reassoc]
theorem normalizationHomology_eulerian (n i : ℕ) :
    eulerianHomologyProjector k A M n i ≫
      HomologicalComplex.homologyMap (normalizationProjection k A M) n =
        HomologicalComplex.homologyMap (normalizationProjection k A M) n ≫
          normalizedEulerianHomologyProjector k A M n i := by
  simp only [eulerianHomologyProjector, normalizedEulerianHomologyProjector,
    ← HomologicalComplex.homologyMap_comp, normalizationProjection_eulerian]

end ModuleCat.Algebra.Hochschild.Symmetric
