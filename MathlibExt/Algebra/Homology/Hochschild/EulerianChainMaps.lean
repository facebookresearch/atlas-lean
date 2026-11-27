/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.Hochschild.SymmetricEulerianBoundary

/-!
# Eulerian weight projections on Hochschild chains

Let k be a commutative ℚ-algebra, A a commutative unital k-algebra,
and M a compatible A-module, viewed as a symmetric bimodule.
In C_n(A,M) = M ⊗[k] A^{⊗n}, the rational permutation action fixes
M and permutes the n algebra factors, with σ acting through
a_j ↦ a_{σ⁻¹(j)}.

The Eulerian chain map E_i has degree-n component given by the
i-th rational Eulerian group-algebra idempotent. The normalization
is bar-lambda: its second operation satisfies
Λ_{2,n} = ∑_{i=0}^{n} 2^i E_{i,n}. On a tensor word Λ_{2,n}
sums the signed shuffles of every prefix/suffix cut, including empty
cuts, with Λ_{2,0} = id.

These component projections commute with the Hochschild boundary.
As chain maps they satisfy E_j E_i = δ_{ij} E_i; in each degree n,
E_{i,n} = 0 for i > n and ∑_{i=0}^{n} E_{i,n} = id.

Reference: J.-L. Loday, Cyclic Homology, §4.5.
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

/-- Let k be a commutative ℚ-algebra, A a commutative unital k-algebra,
and M an A-module with a compatible k-linear action, viewed as a
symmetric bimodule.
The Eulerian weight-i endomorphism E_i of C_*(A,M) acts in
C_n = M ⊗[k] A^{⊗n} by the i-th rational Eulerian
idempotent in ℚ[S_n], fixing M and permuting the algebra factors.
The normalization is Λ_{2,n} = ∑_{j=0}^{n} 2^j E_{j,n}
for the full-cut signed bar-lambda operation. -/
def eulerianChainMap (i : ℕ) : chainComplex k A M ⟶ chainComplex k A M :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (coefficientEulerianOperator k A M n i)) (by
    intro n
    apply ModuleCat.hom_ext
    exact coefficientEulerian_boundary k A M n i)

/-- Let k be a commutative ℚ-algebra, A a commutative unital k-algebra,
and M an A-module with a compatible k-linear action, viewed as a
symmetric bimodule.
The degree-n component of the Eulerian chain map E_i is the
coefficient-fixed rational permutation operator ρ_n(e_n^{(i)}).
Here e_n^{(i)} is the Eulerian idempotent with bar-lambda weight i,
and ρ_n(σ)(m ⊗ tprod(a)) = m ⊗ tprod(a ∘ σ⁻¹). -/
theorem eulerianChainMap_f (n i : ℕ) :
    ((eulerianChainMap k A M i).f n).hom = coefficientEulerianOperator k A M n i := rfl

/-- Let k be a commutative ℚ-algebra, A a commutative unital k-algebra,
and M an A-module with a compatible k-linear action, viewed as a
symmetric bimodule.
The Eulerian chain endomorphisms are orthogonal idempotents:
E_j E_i = E_i when i = j, and E_j E_i = 0 when i ≠ j. -/
theorem eulerianChainMap_comp (i j : ℕ) :
    eulerianChainMap k A M i ≫ eulerianChainMap k A M j =
      if i = j then eulerianChainMap k A M i else 0 := by
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl]
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (coefficientEulerianOperator k A M n i).comp (coefficientEulerianOperator k A M n i) =
      coefficientEulerianOperator k A M n i
    simpa only [ite_eq_left rfl, ite_true] using (coefficientEulerian_projector_laws k A M n).2 i i
  · rw [ite_eq_right h]
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    change (coefficientEulerianOperator k A M n j).comp (coefficientEulerianOperator k A M n i) = 0
    simpa only [ite_eq_right (Ne.symm h)] using (coefficientEulerian_projector_laws k A M n).2 j i

/-- Let k be a commutative ℚ-algebra, A a commutative unital k-algebra,
and M an A-module with a compatible k-linear action, viewed as a
symmetric bimodule.
In Hochschild degree n, the component of Eulerian weight i is
zero whenever n < i: E_{i,n} = 0. -/
theorem eulerianChainMap_support (n i : ℕ) (h : n < i) : (eulerianChainMap k A M i).f n = 0 := by
  apply ModuleCat.hom_ext
  rw [eulerianChainMap_f, coefficientEulerian_outside k A M n i h]
  rfl

/-- Let k be a commutative ℚ-algebra, A a commutative unital k-algebra,
and M an A-module with a compatible k-linear action, viewed as a
symmetric bimodule.
For each Hochschild degree n, the finite family of Eulerian
components satisfies ∑_{i=0}^{n} E_{i,n} = id_{C_n(A,M)}. -/
theorem eulerianChainMap_sum (n : ℕ) :
    (∑ i : Fin (n + 1), (eulerianChainMap k A M i.val).f n) = 𝟙 ((chainComplex k A M).X n) := by
  apply ModuleCat.hom_ext
  simp only [ModuleCat.hom_sum, ModuleCat.hom_id, eulerianChainMap_f]
  change (∑ i : Fin (n + 1), coefficientEulerianOperator k A M n i.val) = LinearMap.id
  exact (coefficientEulerian_projector_laws k A M n).1

end ModuleCat.Algebra.Hochschild.Symmetric
