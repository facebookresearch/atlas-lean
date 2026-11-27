/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import MathlibExt.CategoryTheory.Linear.LocallyFiniteSplitCoproduct

/-!
# Degreewise finite splittings of complex coproducts

Let C be an abelian category with countable coproducts, and let K and
F_j, j ∈ ℕ, be complexes of any common shape on ι. Suppose chain maps
i_j : F_j → K and p_j : K → F_j satisfy
p_j ∘ i_j = id_(F_j) and p_k ∘ i_j = 0 for j ≠ k.
Let N : ι → ℕ bound the projections, so (p_j)_n = 0 for j > N(n),
and assume ∑_(j=0)^(N(n)) (i_j)_n ∘ (p_j)_n = id_(K_n).

The coproduct map D : ⨁_j F_j → K has restriction i_j.
Its inverse in degree n is
V_n = ∑_(j=0)^(N(n)) ι_(j,n) ∘ (p_j)_n.
The completeness identity gives D_n V_n = id_(K_n), and the split,
cross and support identities give V_n D_n = id.
Thus D is a complex isomorphism. The support bound may vary with n,
and the object, morphism and complex-index worlds are independent.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

universe u v w

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasColimitsOfShape (Discrete ℕ) C]
  {ι : Type w} {c : ComplexShape ι}
  (K : HomologicalComplex C c) (F : ℕ → HomologicalComplex C c)
  (i : ∀ j : ℕ, F j ⟶ K) (p : ∀ j : ℕ, K ⟶ F j)
  (hsplit : ∀ j : ℕ, i j ≫ p j = 𝟙 (F j))
  (hcross : ∀ j k : ℕ, j ≠ k → i j ≫ p k = 0)
  (N : ι → ℕ)
  (hsupport : ∀ n : ι, ∀ j : ℕ, N n < j → (p j).f n = 0)
  (hsum : ∀ n : ι, (∑ j : Fin (N n + 1), (p j).f n ≫ (i j).f n) = 𝟙 (K.X n))

/-- For complexes F_j and K of a common shape in an abelian
category C with countable coproducts, chain maps i_j : F_j → K
define D : ⨁_(j∈ℕ) F_j → K by D ∘ ι_j = i_j.
No projection or splitting data is needed to define this map. -/
def splitComplexCoproductMap : (∐ F) ⟶ K := Sigma.desc i

/-- For complexes F_j and K in an abelian category with
countable coproducts, projections p_j : K → F_j and a bound
N : ι → ℕ define V_n : K_n → (⨁_j F_j)_n by
V_n = ∑_(j=0)^(N(n)) ι_(j,n) ∘ (p_j)_n.
This is the degreewise inverse formula when the splitting identities
hold. -/
def splitComplexCoproductInverseAt (n : ι) : K.X n ⟶ (∐ F).X n :=
  ∑ j : Fin (N n + 1), (p j.val).f n ≫ (Sigma.ι F j.val).f n

/-- For chain maps i_j : F_j → K in an abelian category with
countable coproducts, the component D_n of the induced coproduct
map satisfies D_n ∘ ι_(j,n) = (i_j)_n for every j and n.
The complexes may have any common shape. -/
@[reassoc]
theorem splitComplexCoproduct_leg (j : ℕ) (n : ι) :
    (Sigma.ι F j).f n ≫ (splitComplexCoproductMap K F i).f n = (i j).f n := by
  exact congrArg (fun f => f.f n) (Sigma.ι_comp_desc i j)

include hsum in
/-- For complexes F_j,K in an abelian category with countable
coproducts, let D be induced by i_j and
V_n = ∑_(j=0)^(N(n)) ι_(j,n) ∘ (p_j)_n.
If ∑_(j=0)^(N(n)) (i_j)_n ∘ (p_j)_n = id_(K_n), then
D_n ∘ V_n = id_(K_n). The finite completeness condition supplies
this right-inverse identity. -/
@[reassoc]
theorem splitComplexCoproductInverseAt_map (n : ι) :
    splitComplexCoproductInverseAt K F p N n ≫ (splitComplexCoproductMap K F i).f n = 𝟙 (K.X n) := by
  rw [splitComplexCoproductInverseAt, Preadditive.sum_comp]
  simp only [Category.assoc, splitComplexCoproduct_leg]
  exact hsum n

include hsplit hcross hsupport in
/-- For complexes F_j,K in an abelian category with countable
coproducts, suppose p_j ∘ i_j = id_(F_j),
p_k ∘ i_j = 0 for j ≠ k and (p_j)_n = 0 for j > N(n).
Then V_n ∘ D_n = id_((⨁_j F_j)_n), where
D restricts to i_j and V_n = ∑_(j=0)^(N(n)) ι_(j,n) ∘ (p_j)_n.
This identity uses the split, cross and degree-support conditions. -/
@[reassoc]
theorem splitComplexCoproductMap_inverseAt (n : ι) :
    (splitComplexCoproductMap K F i).f n ≫ splitComplexCoproductInverseAt K F p N n =
      𝟙 ((∐ F).X n) := by
  let E := HomologicalComplex.eval C c n
  have hc : IsColimit (E.mapCocone (colimit.cocone (Discrete.functor F))) :=
    isColimitOfPreserves E (colimit.isColimit (Discrete.functor F))
  apply hc.hom_ext
  rintro ⟨j⟩
  change (Sigma.ι F j).f n ≫ ((splitComplexCoproductMap K F i).f n ≫
      splitComplexCoproductInverseAt K F p N n) = (Sigma.ι F j).f n ≫ 𝟙 _
  rw [← Category.assoc, splitComplexCoproduct_leg, splitComplexCoproductInverseAt,
    Preadditive.comp_sum, Category.comp_id]
  by_cases hj : j ≤ N n
  · let j₀ : Fin (N n + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
    rw [Finset.sum_eq_single j₀]
    · have h := congrArg (fun f => f.f n) (hsplit j)
      simpa only [j₀, Category.assoc, HomologicalComplex.comp_f,
        HomologicalComplex.id_f, Category.id_comp] using
        congrArg (fun f => f ≫ (Sigma.ι F j).f n) h
    · intro k hk hne
      have hjk : j ≠ k.val := fun h => hne (Fin.ext h.symm)
      have h := congrArg (fun f => f.f n) (hcross j k.val hjk)
      rw [← Category.assoc, ← HomologicalComplex.comp_f, h, HomologicalComplex.zero_f, zero_comp]
    · simp
  · have hj' : N n < j := Nat.lt_of_not_ge hj
    have hid : 𝟙 ((F j).X n) = 0 := by
      have h := congrArg (fun f => f.f n) (hsplit j)
      rw [HomologicalComplex.comp_f, hsupport n j hj', comp_zero, HomologicalComplex.id_f] at h
      exact h.symm
    have hleg : (Sigma.ι F j).f n = 0 := by
      rw [← Category.id_comp ((Sigma.ι F j).f n), hid, zero_comp]
    rw [hleg]
    apply Finset.sum_eq_zero
    intro k hk
    have hjk : j ≠ k.val := by have hkn := k.isLt; omega
    have h := congrArg (fun f => f.f n) (hcross j k.val hjk)
    rw [← Category.assoc, ← HomologicalComplex.comp_f, h, HomologicalComplex.zero_f, zero_comp]

include hsplit hcross hsupport hsum in
/-- For complexes F_j,K of any common shape in an abelian
category with countable coproducts, assume split orthogonality
p_j i_j = id and p_k i_j = 0 for j ≠ k, the bound
(p_j)_n = 0 for j > N(n), and finite completeness
∑_(j=0)^(N(n)) (i_j)_n(p_j)_n = id_(K_n).
Then every D_n : (⨁_j F_j)_n → K_n is an isomorphism, with inverse
∑_(j=0)^(N(n)) ι_(j,n)(p_j)_n. -/
theorem isIso_splitComplexCoproductMap_f (n : ι) :
    IsIso ((splitComplexCoproductMap K F i).f n) := by
  let e : (∐ F).X n ≅ K.X n :=
    { hom := (splitComplexCoproductMap K F i).f n
      inv := splitComplexCoproductInverseAt K F p N n
      hom_inv_id := splitComplexCoproductMap_inverseAt K F i p hsplit hcross N hsupport n
      inv_hom_id := splitComplexCoproductInverseAt_map K F i p N hsum n }
  exact e.isIso_hom

include hsplit hcross hsupport hsum in
/-- Let C be abelian with countable coproducts and let F_j,K
be complexes of any common shape. If the chain maps i_j,p_j split
orthogonally, (p_j)_n vanishes for j > N(n), and
∑_(j=0)^(N(n)) (i_j)_n ∘ (p_j)_n = id_(K_n), then the coproduct
map with restrictions i_j is an isomorphism ⨁_j F_j ≅ K.
The inverse has the stated finite projection formula in each degree. -/
def locallyFiniteSplitComplexCoproductIso : (∐ F) ≅ K := by
  letI : ∀ n : ι, IsIso ((splitComplexCoproductMap K F i).f n) :=
    fun n => isIso_splitComplexCoproductMap_f K F i p hsplit hcross N hsupport hsum n
  letI := HomologicalComplex.Hom.isIso_of_components (splitComplexCoproductMap K F i)
  exact asIso (splitComplexCoproductMap K F i)

end HomologicalComplex
