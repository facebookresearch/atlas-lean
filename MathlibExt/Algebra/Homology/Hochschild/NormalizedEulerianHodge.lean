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
# The rational Hodge decomposition of normalized chains

Let `k` be a commutative `ℚ`-algebra, `A` a commutative `k`-algebra, and `M` a compatible
symmetric `A`-module. The normalized Eulerian chain projectors are orthogonal and locally
finite: in degree `n`, only weights `0 ≤ i ≤ n` can occur and their sum is the identity.
Weight zero is the identity in degree zero and vanishes in positive degrees.

The image complexes give a coproduct decomposition of the normalized chain complex and of its
homology. The forward maps are the sums of image inclusions and their induced homology maps.
Factorwise normalization intertwines the full and normalized Eulerian projectors, both on
chains and on homology.
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

/-- The normalized Eulerian projector in degree zero.

The weight-zero operator on the degree-zero normalized coefficient module is the identity. -/
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

/-- Vanishing of normalized weight zero in positive degrees.

For `n>0`, the weight-zero normalized Eulerian operator is zero. -/
theorem normalizedEulerianOperator_zero_weight (n : ℕ) (hn : 0 < n) :
    normalizedEulerianOperator k A M n 0 = 0 := by
  unfold normalizedEulerianOperator Equiv.Perm.eulerianElement
  simp_rw [Equiv.Perm.eulerianCoefficient_zero_weight n _ hn, MonoidAlgebra.single_zero]
  rw [Finset.sum_const_zero, map_zero]

/-- The component formula for a normalized Eulerian chain projector.

The degree-`n` component of the weight-`i` chain map is the normalized Eulerian operator
`E_n^i`. -/
theorem normalizedEulerianChainMap_f (n i : ℕ) :
    ((normalizedEulerianChainMap k A M i).f n).hom = normalizedEulerianOperator k A M n i := rfl

/-- Orthogonality of normalized Eulerian chain projectors.

The composite of weight-`i` and weight-`j` chain maps is the weight-`i` map if `i=j`, and zero
otherwise. -/
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

/-- The degree support of a normalized Eulerian chain projector.

The degree-`n` component of weight `i` is zero whenever `n<i`. -/
theorem normalizedEulerianChainMap_support (n i : ℕ) (h : n < i) :
    (normalizedEulerianChainMap k A M i).f n = 0 := by
  apply ModuleCat.hom_ext
  rw [normalizedEulerianChainMap_f, normalizedEulerianOperator_outside k A M n i h]
  rfl

/-- The degreewise completeness of normalized Eulerian chain maps.

The sum of their degree-`n` components over `0 ≤ i ≤ n` is the identity on the normalized
chain term. -/
theorem normalizedEulerianChainMap_sum (n : ℕ) :
    (∑ i : Fin (n + 1), (normalizedEulerianChainMap k A M i.val).f n) =
      𝟙 ((normalizedChainComplex k A M).X n) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_id, normalizedEulerianChainMap_f]
  change (∑ i : Fin (n + 1), normalizedEulerianOperator k A M n i.val) = LinearMap.id
  exact normalizedEulerianOperator_sum k A M n

/-- The normalized Eulerian image complex of one weight.

For `i ∈ ℕ`, this is the image of the normalized Eulerian weight-`i` chain projector. -/
def normalizedEulerianImageComplex (i : ℕ) : ChainComplex (ModuleCat.{max u v w} k) ℕ :=
  image (normalizedEulerianChainMap k A M i)

/-- The coproduct decomposition of normalized Hochschild chains by weight.

The coproduct of normalized Eulerian image complexes is isomorphic to the normalized
Hochschild complex, using local finiteness and the complete orthogonal projector family. -/
def normalizedHodgeComplexIso :
    (∐ (fun i : ℕ => normalizedEulerianImageComplex k A M i)) ≅ normalizedChainComplex k A M :=
  HomologicalComplex.locallyFiniteIdempotentImageComplexIso
    (normalizedChainComplex k A M) (normalizedEulerianChainMap k A M)
    (normalizedEulerianChainMap_comp k A M) id
    (normalizedEulerianChainMap_support k A M) (normalizedEulerianChainMap_sum k A M)

/-- The image-inclusion map of the normalized Hodge decomposition.

The forward chain isomorphism is induced from the coproduct by the image inclusion of each
normalized Eulerian chain projector. -/
theorem normalizedHodgeComplexIso_hom :
    (normalizedHodgeComplexIso k A M).hom =
      Sigma.desc (fun i => image.ι (normalizedEulerianChainMap k A M i)) := rfl

/-- The normalized Hodge coproduct decomposition on homology.

In every degree `n`, the coproduct of the homology objects of the normalized Eulerian image
complexes is isomorphic to normalized Hochschild homology. -/
def normalizedHodgeHomologyIso (n : ℕ) :
    (∐ (fun i : ℕ => (normalizedEulerianImageComplex k A M i).homology n)) ≅
      (normalizedChainComplex k A M).homology n :=
  HomologicalComplex.locallyFiniteIdempotentImageHomologyIso
    (normalizedChainComplex k A M) (normalizedEulerianChainMap k A M)
    (normalizedEulerianChainMap_comp k A M) id
    (normalizedEulerianChainMap_support k A M) (normalizedEulerianChainMap_sum k A M) n

/-- The homology-inclusion map of the normalized Hodge decomposition.

The forward homology decomposition map is induced by the homology maps of the normalized
Eulerian image inclusions. -/
theorem normalizedHodgeHomologyIso_hom (n : ℕ) :
    (normalizedHodgeHomologyIso k A M n).hom = Sigma.desc
      (fun i => HomologicalComplex.homologyMap (image.ι (normalizedEulerianChainMap k A M i)) n) := rfl

/-- The normalized Eulerian projector on a homology degree.

Take the degree-`n` homology map of the weight-`i` normalized chain projector. -/
def normalizedEulerianHomologyProjector (n i : ℕ) :
    (normalizedChainComplex k A M).homology n ⟶ (normalizedChainComplex k A M).homology n :=
  HomologicalComplex.homologyMap (normalizedEulerianChainMap k A M i) n

/-- Orthogonality of normalized Eulerian homology projectors.

In a fixed homology degree, the weight projectors compose to the same projector for equal
weights and to zero for distinct weights. -/
theorem normalizedEulerianHomologyProjector_comp (n i j : ℕ) :
    normalizedEulerianHomologyProjector k A M n i ≫ normalizedEulerianHomologyProjector k A M n j =
      if i = j then normalizedEulerianHomologyProjector k A M n i else 0 := by
  rw [normalizedEulerianHomologyProjector, normalizedEulerianHomologyProjector,
    ← HomologicalComplex.homologyMap_comp, normalizedEulerianChainMap_comp]
  split_ifs
  · rfl
  · exact HomologicalComplex.homologyMap_zero
      (K := normalizedChainComplex k A M) (L := normalizedChainComplex k A M) (i := n)

/-- The chain-level Eulerian naturality of normalization.

The full weight-`i` chain projector followed by normalization equals normalization followed by
the normalized weight-`i` projector. -/
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

/-- The homology-level Eulerian naturality of normalization.

The normalization homology map intertwines the full and normalized Eulerian projectors of the
same weight. -/
@[reassoc]
theorem normalizationHomology_eulerian (n i : ℕ) :
    eulerianHomologyProjector k A M n i ≫
      HomologicalComplex.homologyMap (normalizationProjection k A M) n =
        HomologicalComplex.homologyMap (normalizationProjection k A M) n ≫
          normalizedEulerianHomologyProjector k A M n i := by
  simp only [eulerianHomologyProjector, normalizedEulerianHomologyProjector,
    ← HomologicalComplex.homologyMap_comp, normalizationProjection_eulerian]

end ModuleCat.Algebra.Hochschild.Symmetric
