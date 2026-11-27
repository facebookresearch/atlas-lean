/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianBoundary
public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianAlgebraLevels

/-!
# A-linear raw and normalized Eulerian chain maps

Let k be a commutative ℚ-algebra, A a commutative k-algebra and M a compatible A-module. The
degree-n coefficient Eulerian projectors eₙ⁽ⁱ⁾ commute with the Hochschild boundary, so each
weight defines an A-linear chain endomorphism. They are orthogonal and sum to the identity in
each degree. Normalization with ground tails A/(k·1) intertwines the raw and normalized
operators. Their zero-plus-first sum pₙ=eₙ⁽⁰⁾+eₙ⁽¹⁾ is also a chain projector.

See J.-L. Loday, Cyclic Homology, 2nd ed., §4.5, for the rational Hodge decomposition of
commutative Hochschild chains.
-/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped TensorProduct BigOperators

universe u v w

namespace ModuleCat.Algebra.Hochschild.Symmetric

variable (k : Type u) [CommRing k] [Algebra ℚ k]
  (A : Type v) [CommRing A] [Algebra k A]
  (M : Type w) [AddCommGroup M] [Module k M] [Module A M]
  [SMulCommClass k A M] [IsScalarTower k A M]

/-- The raw A-linear Eulerian operators sum to the identity.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, ∑ᵢ₌₀ⁿ
eₙ⁽ⁱ⁾ = id on M ⊗[k] A⊗n. -/
theorem algebraEulerianOperator_sum (n : ℕ) :
    (∑ i : Fin (n + 1), algebraEulerianOperator k A M n i.val) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro x
  have hi (i : ℕ) : algebraEulerianOperator k A M n i x =
      coefficientEulerianOperator k A M n i x :=
    DFunLike.congr_fun (algebraEulerianOperator_restrictScalars k A M n i) x
  have h := DFunLike.congr_fun (coefficientEulerian_projector_laws k A M n).1 x
  simpa only [LinearMap.sum_apply, LinearMap.id_apply, hi] using h

/-- Orthogonality of raw A-linear Eulerian weights.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, eₙ⁽ⁱ⁾ ∘
eₙ⁽ʲ⁾ is eₙ⁽ⁱ⁾ when i=j and zero otherwise. -/
theorem algebraEulerianOperator_comp (n i j : ℕ) :
    (algebraEulerianOperator k A M n i).comp (algebraEulerianOperator k A M n j) =
      if i = j then algebraEulerianOperator k A M n i else 0 := by
  apply LinearMap.restrictScalars_injective k
  by_cases hij : i = j
  · simp only [if_pos hij, LinearMap.restrictScalars_comp,
      algebraEulerianOperator_restrictScalars]
    simpa only [if_pos hij] using (coefficientEulerian_projector_laws k A M n).2 i j
  · simp only [if_neg hij, LinearMap.restrictScalars_comp,
      LinearMap.restrictScalars_zero, algebraEulerianOperator_restrictScalars]
    simpa only [if_neg hij] using (coefficientEulerian_projector_laws k A M n).2 i j

/-- Raw algebra-linear Eulerian weights above degree n vanish.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, eₙ⁽ⁱ⁾=0
whenever n<i. -/
theorem algebraEulerianOperator_outside (n i : ℕ) (hi : n < i) :
    algebraEulerianOperator k A M n i = 0 := by
  apply LinearMap.restrictScalars_injective k
  simpa only [algebraEulerianOperator_restrictScalars, LinearMap.restrictScalars_zero] using
    coefficientEulerian_outside k A M n i hi

/-- The normalized A-linear Eulerian weights sum to the identity.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, ∑ᵢ₌₀ⁿ
ēₙ⁽ⁱ⁾ = id on M ⊗[k] (A/(k·1))⊗n. -/
theorem algebraNormalizedEulerianOperator_sum (n : ℕ) :
    (∑ i : Fin (n + 1), algebraNormalizedEulerianOperator k A M n i.val) = LinearMap.id := by
  classical
  let ρ := TensorPower.coefficientRationalPermutationAction (k := k) (M := M)
    (V := ModuleCat.Algebra.Hochschild.quotientCarrier k A) n
  have h : (∑ i : Fin (n + 1), ρ (Equiv.Perm.eulerianElement n i.val)) = LinearMap.id := by
    change (∑ i : Fin (n + 1), ρ (Equiv.Perm.eulerianElement n i.val)) = 1
    rw [← map_sum, (Equiv.Perm.eulerianElement_projector_laws n).1, map_one]
  apply LinearMap.ext
  intro x
  have hi (i : ℕ) : algebraNormalizedEulerianOperator k A M n i x =
      ρ (Equiv.Perm.eulerianElement n i) x :=
    DFunLike.congr_fun (algebraNormalizedEulerianOperator_restrictScalars k A M n i) x
  simpa only [LinearMap.sum_apply, LinearMap.id_apply, hi] using DFunLike.congr_fun h x

/-- Orthogonality of normalized A-linear Eulerian weights.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, ēₙ⁽ⁱ⁾ ∘
ēₙ⁽ʲ⁾ is ēₙ⁽ⁱ⁾ when i=j and zero otherwise. -/
theorem algebraNormalizedEulerianOperator_comp (n i j : ℕ) :
    (algebraNormalizedEulerianOperator k A M n i).comp
        (algebraNormalizedEulerianOperator k A M n j) =
      if i = j then algebraNormalizedEulerianOperator k A M n i else 0 := by
  let ρ := TensorPower.coefficientRationalPermutationAction (k := k) (M := M)
    (V := ModuleCat.Algebra.Hochschild.quotientCarrier k A) n
  apply LinearMap.restrictScalars_injective k
  by_cases hij : i = j
  · simp only [if_pos hij, LinearMap.restrictScalars_comp,
      algebraNormalizedEulerianOperator_restrictScalars]
    change ρ (Equiv.Perm.eulerianElement n i) * ρ (Equiv.Perm.eulerianElement n j) =
      ρ (Equiv.Perm.eulerianElement n i)
    rw [← map_mul, (Equiv.Perm.eulerianElement_projector_laws n).2 i j, if_pos hij]
  · simp only [if_neg hij, LinearMap.restrictScalars_comp, LinearMap.restrictScalars_zero,
      algebraNormalizedEulerianOperator_restrictScalars]
    change ρ (Equiv.Perm.eulerianElement n i) * ρ (Equiv.Perm.eulerianElement n j) = 0
    rw [← map_mul, (Equiv.Perm.eulerianElement_projector_laws n).2 i j, if_neg hij, map_zero]

/-- Normalized algebra-linear Eulerian weights above degree n vanish.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, ēₙ⁽ⁱ⁾=0
whenever n<i. -/
theorem algebraNormalizedEulerianOperator_outside (n i : ℕ) (hi : n < i) :
    algebraNormalizedEulerianOperator k A M n i = 0 := by
  apply LinearMap.restrictScalars_injective k
  simp only [algebraNormalizedEulerianOperator_restrictScalars, LinearMap.restrictScalars_zero,
    Equiv.Perm.eulerianElement_outside n i hi, map_zero]

/-- The raw A-linear Eulerian boundary square.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, bₙ ∘
eₙ₊₁⁽ⁱ⁾ = eₙ⁽ⁱ⁾ ∘ bₙ, with bₙ mapping degree n+1 to n. -/
theorem algebraEulerianOperator_boundary (n i : ℕ) :
    (algebraBoundary k A M n).comp (algebraEulerianOperator k A M (n + 1) i) =
      (algebraEulerianOperator k A M n i).comp (algebraBoundary k A M n) := by
  have h : ((algebraBoundary k A M n).restrictScalars k).comp
      (coefficientEulerianOperator k A M (n + 1) i) =
    (coefficientEulerianOperator k A M n i).comp ((algebraBoundary k A M n).restrictScalars k) :=
    coefficientEulerian_boundary k A M n i
  apply LinearMap.restrictScalars_injective k
  simpa only [LinearMap.restrictScalars_comp, algebraEulerianOperator_restrictScalars] using h

/-- The normalized A-linear Eulerian boundary square.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the
normalized boundary satisfies b̄ₙ ∘ ēₙ₊₁⁽ⁱ⁾ = ēₙ⁽ⁱ⁾ ∘ b̄ₙ. -/
theorem algebraNormalizedEulerianOperator_boundary (n i : ℕ) :
    (algebraNormalizedBoundary k A M n).comp (algebraNormalizedEulerianOperator k A M (n + 1) i) =
      (algebraNormalizedEulerianOperator k A M n i).comp (algebraNormalizedBoundary k A M n) := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := algebraNormalizationLevelMap_surjective k A M (n + 1) y
  have hq (z : M ⊗[k] TensorPower k (n + 1) A) :
      algebraNormalizedBoundary k A M n (algebraNormalizationLevelMap k A M (n + 1) z) =
        algebraNormalizationLevelMap k A M n (algebraBoundary k A M n z) :=
    nativeNormalizationBoundary_apply k A M n z
  change algebraNormalizedBoundary k A M n
      (algebraNormalizedEulerianOperator k A M (n + 1) i
        (algebraNormalizationLevelMap k A M (n + 1) x)) =
    algebraNormalizedEulerianOperator k A M n i
      (algebraNormalizedBoundary k A M n (algebraNormalizationLevelMap k A M (n + 1) x))
  have hs := DFunLike.congr_fun (algebraNormalizationLevelMap_eulerian k A M (n + 1) i) x
  have hb := DFunLike.congr_fun (algebraEulerianOperator_boundary k A M n i) x
  have ht := DFunLike.congr_fun (algebraNormalizationLevelMap_eulerian k A M n i)
    (algebraBoundary k A M n x)
  simp only [LinearMap.comp_apply] at hs hb ht
  rw [← hs, hq, hb, ht, ← hq]

/-- The raw Hochschild chain endomorphism of one Eulerian weight.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, weight i
acts in chain degree n by algebraEulerianOperator(n,i), giving an endomorphism of
algebraRawComplex. -/
def algebraEulerianChainMap (i : ℕ) : algebraRawComplex k A M ⟶ algebraRawComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraEulerianOperator k A M n i)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M ⊗[k] TensorPower k (n + 1) A at x
    dsimp only [algebraRawComplex]
    rw [ChainComplex.of_d]
    change algebraBoundary k A M n (algebraEulerianOperator k A M (n + 1) i x) =
      algebraEulerianOperator k A M n i (algebraBoundary k A M n x)
    exact congrArg (fun f : M ⊗[k] TensorPower k (n + 1) A →ₗ[A]
      M ⊗[k] TensorPower k n A => f x) (algebraEulerianOperator_boundary k A M n i))

/-- The degree-n component of the raw Eulerian chain map.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the nth
component of algebraEulerianChainMap(i) is eₙ⁽ⁱ⁾. -/
theorem algebraEulerianChainMap_f (n i : ℕ) :
    ((algebraEulerianChainMap k A M i).f n).hom = algebraEulerianOperator k A M n i := rfl

/-- The normalized Hochschild chain endomorphism of one Eulerian weight.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, weight i
acts in degree n by ēₙ⁽ⁱ⁾ on the normalized coefficient tensor complex. -/
def algebraNormalizedEulerianChainMap (i : ℕ) :
    algebraNormalizedChainComplex k A M ⟶ algebraNormalizedChainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (algebraNormalizedEulerianOperator k A M n i)) (by
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) at x
    dsimp only [algebraNormalizedChainComplex]
    rw [ChainComplex.of_d]
    change algebraNormalizedBoundary k A M n (algebraNormalizedEulerianOperator k A M (n + 1) i x) =
      algebraNormalizedEulerianOperator k A M n i (algebraNormalizedBoundary k A M n x)
    exact congrArg (fun f :
      M ⊗[k] TensorPower k (n + 1) (ModuleCat.Algebra.Hochschild.quotientCarrier k A) →ₗ[A]
      M ⊗[k] TensorPower k n (ModuleCat.Algebra.Hochschild.quotientCarrier k A) => f x)
        (algebraNormalizedEulerianOperator_boundary k A M n i))

/-- The component of the normalized Eulerian chain endomorphism.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the nth
component of algebraNormalizedEulerianChainMap(i) is algebraNormalizedEulerianOperator(n,i). -/
theorem algebraNormalizedEulerianChainMap_f (n i : ℕ) :
    ((algebraNormalizedEulerianChainMap k A M i).f n).hom =
      algebraNormalizedEulerianOperator k A M n i := rfl

/-- The normalization chain map intertwines raw and normalized Eulerian weights.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M,
normalization followed by the normalized weight-i map equals the raw weight-i map followed by
normalization. -/
@[reassoc]
theorem algebraNormalizationProjection_eulerian (i : ℕ) :
    algebraNormalizationProjection k A M ≫ algebraNormalizedEulerianChainMap k A M i =
      algebraEulerianChainMap k A M i ≫ algebraNormalizationProjection k A M := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  change (algebraNormalizedEulerianOperator k A M n i).comp (algebraNormalizationLevelMap k A M n) =
    (algebraNormalizationLevelMap k A M n).comp (algebraEulerianOperator k A M n i)
  exact (algebraNormalizationLevelMap_eulerian k A M n i).symm

/-- Orthogonality of raw Eulerian chain endomorphisms.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the
chain maps of weights i and j compose to the weight-i map when i=j and to zero otherwise. -/
theorem algebraEulerianChainMap_comp (i j : ℕ) :
    algebraEulerianChainMap k A M i ≫ algebraEulerianChainMap k A M j =
      if i = j then algebraEulerianChainMap k A M i else 0 := by
  by_cases hij : i = j
  · rw [if_pos hij]
    subst j
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (algebraEulerianOperator k A M n i).comp (algebraEulerianOperator k A M n i) =
      algebraEulerianOperator k A M n i
    exact (algebraEulerianOperator_comp k A M n i i).trans (if_pos rfl)
  · rw [if_neg hij]
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (algebraEulerianOperator k A M n j).comp (algebraEulerianOperator k A M n i) = 0
    exact (algebraEulerianOperator_comp k A M n j i).trans (if_neg (Ne.symm hij))

/-- Orthogonality of normalized Eulerian chain endomorphisms.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the
normalized chain maps of weights i and j compose to the weight-i map when i=j and to zero
otherwise. -/
theorem algebraNormalizedEulerianChainMap_comp (i j : ℕ) :
    algebraNormalizedEulerianChainMap k A M i ≫ algebraNormalizedEulerianChainMap k A M j =
      if i = j then algebraNormalizedEulerianChainMap k A M i else 0 := by
  by_cases hij : i = j
  · rw [if_pos hij]
    subst j
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (algebraNormalizedEulerianOperator k A M n i).comp (algebraNormalizedEulerianOperator k A M n i) =
      algebraNormalizedEulerianOperator k A M n i
    exact (algebraNormalizedEulerianOperator_comp k A M n i i).trans (if_pos rfl)
  · rw [if_neg hij]
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (algebraNormalizedEulerianOperator k A M n j).comp (algebraNormalizedEulerianOperator k A M n i) = 0
    exact (algebraNormalizedEulerianOperator_comp k A M n j i).trans (if_neg (Ne.symm hij))

/-- The raw zero-plus-first Eulerian chain projector.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, sum the
chain maps of weights zero and one; its degree-n component is pₙ=eₙ⁽⁰⁾+eₙ⁽¹⁾. -/
def algebraFirstEulerianChainMap : algebraRawComplex k A M ⟶ algebraRawComplex k A M :=
  algebraEulerianChainMap k A M 0 + algebraEulerianChainMap k A M 1

/-- The normalized zero-plus-first Eulerian chain projector.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the
degree-n component is p̄ₙ=ēₙ⁽⁰⁾+ēₙ⁽¹⁾. -/
def algebraNormalizedFirstEulerianChainMap :
    algebraNormalizedChainComplex k A M ⟶ algebraNormalizedChainComplex k A M :=
  algebraNormalizedEulerianChainMap k A M 0 + algebraNormalizedEulerianChainMap k A M 1

/-- The raw lowest-weight chain projector has component pₙ.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the nth
component of algebraFirstEulerianChainMap is algebraFirstEulerianOperator(n). -/
theorem algebraFirstEulerianChainMap_f (n : ℕ) :
    ((algebraFirstEulerianChainMap k A M).f n).hom = algebraFirstEulerianOperator k A M n := rfl

/-- The normalized lowest-weight chain projector has component p̄ₙ.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the nth
component of algebraNormalizedFirstEulerianChainMap is
algebraNormalizedFirstEulerianOperator(n). -/
theorem algebraNormalizedFirstEulerianChainMap_f (n : ℕ) :
    ((algebraNormalizedFirstEulerianChainMap k A M).f n).hom =
      algebraNormalizedFirstEulerianOperator k A M n := rfl

/-- Normalization intertwines the two lowest-weight chain projectors.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, the raw
and normalized zero-plus-first chain maps commute with algebraNormalizationProjection. -/
@[reassoc]
theorem algebraNormalizationProjection_firstEulerian :
    algebraNormalizationProjection k A M ≫ algebraNormalizedFirstEulerianChainMap k A M =
      algebraFirstEulerianChainMap k A M ≫ algebraNormalizationProjection k A M := by
  simp only [algebraNormalizedFirstEulerianChainMap, algebraFirstEulerianChainMap,
    Preadditive.comp_add, Preadditive.add_comp, algebraNormalizationProjection_eulerian]

/-- The normalized lowest-weight A-linear operator is idempotent.

For a commutative ℚ-algebra k, a commutative k-algebra A and a compatible A-module M, p̄ₙ ∘
p̄ₙ=p̄ₙ on normalized coefficient tensors. -/
theorem algebraNormalizedFirstEulerianOperator_idempotent (n : ℕ) :
    (algebraNormalizedFirstEulerianOperator k A M n).comp
        (algebraNormalizedFirstEulerianOperator k A M n) =
      algebraNormalizedFirstEulerianOperator k A M n := by
  simp only [algebraNormalizedFirstEulerianOperator, LinearMap.add_comp, LinearMap.comp_add,
    algebraNormalizedEulerianOperator_comp, if_pos rfl,
    if_neg (by omega : (0 : ℕ) ≠ 1), if_neg (by omega : (1 : ℕ) ≠ 0), add_zero, zero_add]
  rfl

end ModuleCat.Algebra.Hochschild.Symmetric
