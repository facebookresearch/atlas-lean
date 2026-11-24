/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
This completed proof port retains the original Apache 2.0 license and author credit.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/AlgebraicTopology/SimplicialObject/AlexanderWhitney.lean
Original license: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
Modifications: only module/namespace paths are adapted for Atlas.
Mathematical operations, hypotheses and proof bodies are retained.
-/

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import MathlibExt.CategoryTheory.DGSource.CochainTensorSummands
public import MathlibExt.CategoryTheory.DGSource.CochainTensorDifferential
public import MathlibExt.CategoryTheory.DGSourceMore.SimplexSubinterval
public import MathlibExt.CategoryTheory.DGSource.MonoidalPreadditive

/-!
# The Alexander–Whitney map of simplicial objects

Let `C` be a preadditive monoidal category with finite coproducts, and let `A` and `B` be
simplicial objects in `C`.  Their tensor product `A ⊗ B` is taken degreewise,
`(A ⊗ B)ₙ = Aₙ ⊗ Bₙ`, with the tensor product of the structure maps.  The Alexander–Whitney map
`CategoryTheory.SimplicialObject.alexanderWhitney A B` is the morphism of chain complexes from
the alternating face map complex of `A ⊗ B` to the tensor product of the alternating face map
complexes of `A` and of `B`.  In degree `n` it is
`∑_{p + q = n} A(front p-face) ⊗ B(back q-face)`,
where the front `p`-face of `⦋n⦌` is the inclusion of the vertices `0, …, p` and the back `q`-face
is the inclusion of the vertices `p, …, n`, both given by Mathlib's
`SimplexCategory.subinterval`.  The tensor product of chain complexes is Mathlib's monoidal
structure on `ChainComplex C ℕ`, whose differential is `d (a ⊗ b) = d a ⊗ b + (-1)^p a ⊗ d b`
for `a` of degree `p`.

The simplicial chains of a product of simplicial sets are the case where `A` and `B` are free on
the simplices of the factors (`SSet.alexanderWhitney`).  Singular chains with coefficients in a
local coefficient system form a simplicial module that is not free on the simplices with a fixed
coefficient object, which is why the construction is stated for arbitrary simplicial objects: the
Alexander–Whitney diagonal of chains with local coefficients, along which cup and cap products
with local coefficients are taken, is an instance of it.

The Alexander–Whitney map is coassociative and counital, with counit the identity of `𝟙_ C` in
degree zero, so it makes the alternating face map complex an oplax monoidal functor from
simplicial objects with the degreewise tensor product to chain complexes.  On normalized chains,
the mate of this structure along the Dold–Kan correspondence is the lax monoidal structure of the
Dold–Kan functor from chain complexes to simplicial objects (J. Lurie, *Higher Algebra*,
Construction 1.3.1.13), which underlies the simplicial enrichment of a differential graded
category.

## Main definitions and results

* `CategoryTheory.SimplicialObject.alexanderWhitney`: the Alexander–Whitney chain map.
* `CategoryTheory.SimplicialObject.alexanderWhitney_f`: its degree-`n` component.
* `CategoryTheory.SimplicialObject.alexanderWhitney_naturality`: it is natural in both simplicial
  objects.
* `CategoryTheory.SimplicialObject.alexanderWhitney_coassoc`: it is coassociative.
* `CategoryTheory.SimplicialObject.alternatingFaceMapComplexOplaxMonoidal`: the instance
  `(alternatingFaceMapComplex C).OplaxMonoidal`, with comultiplication the
  Alexander–Whitney map (`CategoryTheory.SimplicialObject.alternatingFaceMapComplex_δ`) and
  counit the identity of `𝟙_ C` in degree zero
  (`CategoryTheory.SimplicialObject.alternatingFaceMapComplex_η_f_zero`).

## References

* S. Eilenberg and J. A. Zilber, *On products of complexes*, Amer. J. Math. 75 (1953).
* C. Weibel, *An Introduction to Homological Algebra*, Section 8.5.
* J. Lurie, *Higher Algebra*, Construction 1.3.1.13.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory AlgebraicTopology Opposite HomologicalComplex

open scoped Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C]

variable [Preadditive C]

variable [MonoidalCategory C] [MonoidalPreadditive C] [HasFiniteCoproducts C]
  (A B : SimplicialObject C)

/-- The summand of the Alexander–Whitney map in degree `n` and bidegree `(p, q)`: the front
`p`-face of `A` tensored with the back `q`-face of `B`, or zero if `p + q ≠ n`.  Indexing by an
arbitrary pair keeps the summands of all bidegrees in one type. -/
private def alexanderWhitneyTerm (n p q : ℕ) :
    A _⦋n⦌ ⊗ B _⦋n⦌ ⟶
      ((alternatingFaceMapComplex C).obj A ⊗ (alternatingFaceMapComplex C).obj B).X n :=
  if h : p + q = n then
    (A.map (SimplexCategory.subinterval 0 p (by omega)).op ⊗ₘ
      B.map (SimplexCategory.subinterval p q (by omega)).op) ≫
        ιTensorObj ((alternatingFaceMapComplex C).obj A) ((alternatingFaceMapComplex C).obj B)
          p q n h
  else 0

private lemma alexanderWhitneyTerm_of_eq (n p q : ℕ) (h : p + q = n) :
    alexanderWhitneyTerm A B n p q =
      (A.map (SimplexCategory.subinterval 0 p (by omega)).op ⊗ₘ
        B.map (SimplexCategory.subinterval p q (by omega)).op) ≫
          ιTensorObj ((alternatingFaceMapComplex C).obj A) ((alternatingFaceMapComplex C).obj B)
            p q n h := by
  simp only [alexanderWhitneyTerm, h, ↓reduceDIte]

/-- The boundary of the Alexander–Whitney map in the bidegree `(r, s)`: the part of `d ∘ AW` that
lands in bidegree `(r, s)` is `AW ∘ d`.  The last face of the front `(r + 1)`-face cancels against
the zeroth face of the back `(s + 1)`-face; every other face of a front or back face is the front
or back face of a face of the simplex. -/
private lemma alexanderWhitneyTerm_D (n r s : ℕ) (h : r + s = n) :
    alexanderWhitneyTerm A B (n + 1) (r + 1) s ≫
        mapBifunctor.D₁ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n +
      alexanderWhitneyTerm A B (n + 1) r (s + 1) ≫
        mapBifunctor.D₂ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        ((A.δ k ⊗ₘ B.δ k) ≫ alexanderWhitneyTerm A B n r s) := by
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ _ (by omega),
    alexanderWhitneyTerm_of_eq _ _ _ _ _ (by omega)]
  simp only [Category.assoc, ChainComplex.ιTensorObj_D₁_succ,
    ChainComplex.ιTensorObj_D₂_succ, Preadditive.comp_zsmul, alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD]
  dsimp only [alternatingFaceMapComplex_obj_X, Monoidal.tensorObj_obj]
  simp only [tensorHom_comp_whiskerRight_assoc, tensorHom_comp_whiskerLeft_assoc,
    Preadditive.comp_sum, Preadditive.comp_zsmul,
    sum_tensor, tensor_sum, zsmul_tensorHom, tensorHom_zsmul, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  have hrs : r + 1 + (s + 1) = n + 2 := by omega
  conv_rhs =>
    rw [← Fin.sum_congr' _ hrs, Fin.sum_univ_add]
  rw [Fin.sum_univ_castSucc (n := r + 1), Fin.sum_univ_succ (n := s + 1)]
  simp only [alexanderWhitneyTerm_of_eq A B n r s h, tensorHom_comp_tensorHom_assoc]
  simp only [SimplicialObject.δ, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ_last_comp_subinterval_zero, SimplexCategory.δ_zero_comp_subinterval]
  rw [smul_add, Finset.smul_sum, add_add_add_comm]
  -- the two sums match termwise, and the two remaining terms cancel
  have key {M : Type _} [AddCommGroup M] {P P' a b Q Q' : M} (h₁ : P = P') (h₂ : Q = Q')
      (h₃ : a + b = 0) : P + b + (a + Q) = P' + Q' := by
    have hadd : P + b + (a + Q) = P + Q + (a + b) := by abel
    rw [← h₁, ← h₂, hadd, h₃, add_zero]
  refine key ?_ ?_ ?_
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    have := i.isLt
    rw [SimplexCategory.δ_comp_subinterval_zero i.castSucc
        (Fin.cast (by omega) (Fin.castAdd (s + 1) i)) (by simp),
      SimplexCategory.subinterval_comp_δ_of_le (j := r) _ (by simp; omega)]
    simp
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [SimplexCategory.δ_succ_comp_subinterval j (Fin.cast (by omega) (Fin.natAdd (r + 1) j))
        (by simp),
      SimplexCategory.subinterval_zero_comp_δ_of_lt (p := r) _ (by simp; omega), smul_smul]
    congr 1
    simp [pow_add]
  · rw [smul_smul, ← add_smul]
    simp [pow_succ]

/-- The degree-`n` component of the Alexander–Whitney map. -/
private def alexanderWhitneyX (n : ℕ) :
    A _⦋n⦌ ⊗ B _⦋n⦌ ⟶
      ((alternatingFaceMapComplex C).obj A ⊗ (alternatingFaceMapComplex C).obj B).X n :=
  ∑ pq ∈ Finset.antidiagonal n, alexanderWhitneyTerm A B n pq.1 pq.2

/-- **The Alexander–Whitney map** of two simplicial objects, from the alternating face map
complex of their degreewise tensor product to the tensor product of their alternating face map
complexes.  In degree `n` it is the sum over `p + q = n` of the front `p`-face of `A` tensored
with the back `q`-face of `B` (`CategoryTheory.SimplicialObject.alexanderWhitney_f`).  It is a
morphism of chain complexes for the Koszul sign convention on the tensor product. -/
def alexanderWhitney :
    (alternatingFaceMapComplex C).obj (A ⊗ B) ⟶
      (alternatingFaceMapComplex C).obj A ⊗ (alternatingFaceMapComplex C).obj B where
  f := alexanderWhitneyX A B
  comm' := by
    rintro _ n rfl
    have hd : ((alternatingFaceMapComplex C).obj A ⊗
        (alternatingFaceMapComplex C).obj B).d (n + 1) n =
        mapBifunctor.D₁ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n +
          mapBifunctor.D₂ _ _ (curriedTensor C) (ComplexShape.down ℕ) (n + 1) n :=
      mapBifunctor.d_eq _ _ _ _ _ _
    -- the faces of `A ⊗ B` are typed as morphisms of tensor products, so that the composites
    -- with the summands of the Alexander–Whitney map can be distributed
    rw [hd, show ((alternatingFaceMapComplex C).obj (A ⊗ B)).d (n + 1) n =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (A.δ i ⊗ₘ B.δ i) :
        A _⦋n + 1⦌ ⊗ B _⦋n + 1⦌ ⟶ A _⦋n⦌ ⊗ B _⦋n⦌) from
      AlternatingFaceMapComplex.obj_d_eq (A ⊗ B) n]
    dsimp only [alexanderWhitneyX, alternatingFaceMapComplex_obj_X, Monoidal.tensorObj_obj]
    simp only [Preadditive.sum_comp, Preadditive.comp_add, Preadditive.zsmul_comp,
      Preadditive.comp_sum]
    rw [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ',
      alexanderWhitneyTerm_of_eq _ _ _ 0 (n + 1) (by omega),
      alexanderWhitneyTerm_of_eq _ _ _ (n + 1) 0 (by omega), Category.assoc, Category.assoc,
      ChainComplex.ιTensorObj_D₁_zero, ChainComplex.ιTensorObj_D₂_zero, comp_zero, comp_zero,
      zero_add, zero_add, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun pq hpq ↦ ?_
    exact alexanderWhitneyTerm_D A B n pq.1 pq.2 (Finset.mem_antidiagonal.mp hpq)

/-- The degree-`n` component of the Alexander–Whitney map: the sum over `p ≤ n` of the front
`p`-face of `A` tensored with the back `(n - p)`-face of `B`. -/
-- The sum is typed as a morphism out of `Aₙ ⊗ Bₙ` rather than out of the degree-`n` term of the
-- alternating face map complex, which is the same object only up to unfolding, so that composites
-- with the summands can be rewritten.
@[simp]
lemma alexanderWhitney_f (n : ℕ) :
    (alexanderWhitney A B).f n =
      (∑ p : Fin (n + 1),
        (A.map (SimplexCategory.subinterval 0 p (by omega)).op ⊗ₘ
          B.map (SimplexCategory.subinterval p (n - p) (by omega)).op) ≫
            ιTensorObj ((alternatingFaceMapComplex C).obj A)
              ((alternatingFaceMapComplex C).obj B) (p : ℕ) (n - p) n (by omega) :
        A _⦋n⦌ ⊗ B _⦋n⦌ ⟶ _) := by
  dsimp only [alexanderWhitney, alexanderWhitneyX]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (alexanderWhitneyTerm A B n),
    Finset.sum_range]
  exact Finset.sum_congr rfl fun p _ ↦ alexanderWhitneyTerm_of_eq _ _ _ _ _ (by omega)

variable {A B} in
/-- The Alexander–Whitney map is natural in both simplicial objects. -/
@[reassoc]
lemma alexanderWhitney_naturality {A' B' : SimplicialObject C} (f : A ⟶ A') (g : B ⟶ B') :
    (alternatingFaceMapComplex C).map (f ⊗ₘ g) ≫ alexanderWhitney A' B' =
      alexanderWhitney A B ≫
        ((alternatingFaceMapComplex C).map f ⊗ₘ (alternatingFaceMapComplex C).map g) := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, alexanderWhitney_f,
    alexanderWhitney_f]
  dsimp only [alternatingFaceMapComplex_obj_X, alternatingFaceMapComplex_map_f,
    Monoidal.tensorObj_obj, Monoidal.tensorHom_app]
  simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [tensorHom_eq_mapBifunctorMap, ι_tensorHom]
  dsimp only [alternatingFaceMapComplex_obj_X, alternatingFaceMapComplex_map_f]
  simp only [tensorHom_comp_tensorHom_assoc, NatTrans.naturality]

/-- The degree-`n` component of the Alexander–Whitney map as the sum of its bidegree summands. -/
private lemma alexanderWhitney_f_eq_sum (n : ℕ) :
    (alexanderWhitney A B).f n =
      ∑ pq ∈ Finset.antidiagonal n, alexanderWhitneyTerm A B n pq.1 pq.2 :=
  rfl

section Coassociativity

variable (D : SimplicialObject C)

/-- The summand of the twice-iterated Alexander–Whitney map in degree `n` and tridegree
`(a, b, c)`, after the associator: the front `a`-face of `A`, the middle `b`-face of `B` and the
back `c`-face of `D`, or zero if `a + (b + c) ≠ n`. -/
private def alexanderWhitneyTerm₃ (n a b c : ℕ) :
    A _⦋n⦌ ⊗ (B _⦋n⦌ ⊗ D _⦋n⦌) ⟶
      ((alternatingFaceMapComplex C).obj A ⊗ ((alternatingFaceMapComplex C).obj B ⊗
        (alternatingFaceMapComplex C).obj D)).X n :=
  if h : a + (b + c) = n then
    (A.map (SimplexCategory.subinterval 0 a (by omega)).op ⊗ₘ
        (B.map (SimplexCategory.subinterval a b (by omega)).op ⊗ₘ
          D.map (SimplexCategory.subinterval (a + b) c (by omega)).op)) ≫
      (A _⦋a⦌ ◁ ιTensorObj ((alternatingFaceMapComplex C).obj B)
        ((alternatingFaceMapComplex C).obj D) b c (b + c) rfl) ≫
      ιTensorObj ((alternatingFaceMapComplex C).obj A)
        ((alternatingFaceMapComplex C).obj B ⊗ (alternatingFaceMapComplex C).obj D) a (b + c) n h
  else 0

/-- The summand of bidegree `(p, c)` of the Alexander–Whitney map of `A ⊗ B` and `D`, followed by
the Alexander–Whitney map of `A` and `B` and the associator, is the sum of the tridegree
summands `(a, b, c)` with `a + b = p`. -/
private lemma alexanderWhitneyTerm_whiskerRight_associator (n p c : ℕ) (h : p + c = n) :
    alexanderWhitneyTerm (A ⊗ B) D n p c ≫
        (alexanderWhitney A B ▷ (alternatingFaceMapComplex C).obj D).f n ≫
          (α_ ((alternatingFaceMapComplex C).obj A) ((alternatingFaceMapComplex C).obj B)
            ((alternatingFaceMapComplex C).obj D)).hom.f n =
      ∑ ab ∈ Finset.antidiagonal p,
        (α_ (A _⦋n⦌) (B _⦋n⦌) (D _⦋n⦌)).hom ≫ alexanderWhitneyTerm₃ A B D n ab.1 ab.2 c := by
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ _ h, Category.assoc, ι_whiskerRight_assoc]
  dsimp only [alternatingFaceMapComplex_obj_X, Monoidal.tensorObj_obj]
  rw [alexanderWhitney_f_eq_sum, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun ab hab ↦ ?_
  obtain rfl : ab.1 + ab.2 = p := Finset.mem_antidiagonal.mp hab
  have hα := ι_ι_associator_hom ((alternatingFaceMapComplex C).obj A)
    ((alternatingFaceMapComplex C).obj B) ((alternatingFaceMapComplex C).obj D) ab.1 ab.2 c _
    (ab.2 + c) n rfl rfl h (by omega)
  dsimp only [alternatingFaceMapComplex_obj_X] at hα
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ _ rfl, alexanderWhitneyTerm₃, dite_eq_left (by omega),
    comp_whiskerRight_assoc, hα]
  simp only [Monoidal.tensorObj_map, ← Category.assoc, ← tensorHom_id, tensorHom_comp_tensorHom,
    Category.comp_id]
  rw [Category.assoc, associator_naturality]
  simp only [Category.assoc, ← Functor.map_comp, ← op_comp,
    MathlibExt.DGSource.SimplexCategory.subinterval_comp_subinterval _ _ _ _ _ _ rfl, Nat.zero_add]

/-- The summand of bidegree `(a, m)` of the Alexander–Whitney map of `A` and `B ⊗ D`, followed by
the Alexander–Whitney map of `B` and `D`, is the sum of the tridegree summands `(a, b, c)` with
`b + c = m`. -/
private lemma alexanderWhitneyTerm_whiskerLeft (n a m : ℕ) (h : a + m = n) :
    alexanderWhitneyTerm A (B ⊗ D) n a m ≫
        ((alternatingFaceMapComplex C).obj A ◁ alexanderWhitney B D).f n =
      ∑ bc ∈ Finset.antidiagonal m, alexanderWhitneyTerm₃ A B D n a bc.1 bc.2 := by
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ _ h, Category.assoc, ι_whiskerLeft]
  dsimp only [alternatingFaceMapComplex_obj_X, Monoidal.tensorObj_obj]
  rw [alexanderWhitney_f_eq_sum, whiskerLeft_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun bc hbc ↦ ?_
  obtain rfl : bc.1 + bc.2 = m := Finset.mem_antidiagonal.mp hbc
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ _ rfl, alexanderWhitneyTerm₃, dite_eq_left h]
  simp only [Monoidal.tensorObj_map, ← Category.assoc, ← id_tensorHom, tensorHom_comp_tensorHom,
    Category.comp_id]
  simp only [← Functor.map_comp, ← op_comp,
    MathlibExt.DGSource.SimplexCategory.subinterval_comp_subinterval _ _ _ _ _ _ rfl, Nat.add_zero]

/-- **Coassociativity of the Alexander–Whitney map**: the two ways of splitting a simplex into
a front, a middle and a back face agree, up to the associators of simplicial objects and of
chain complexes. -/
@[reassoc]
lemma alexanderWhitney_coassoc :
    alexanderWhitney (A ⊗ B) D ≫ alexanderWhitney A B ▷ (alternatingFaceMapComplex C).obj D ≫
        (α_ ((alternatingFaceMapComplex C).obj A) ((alternatingFaceMapComplex C).obj B)
          ((alternatingFaceMapComplex C).obj D)).hom =
      (alternatingFaceMapComplex C).map (α_ A B D).hom ≫ alexanderWhitney A (B ⊗ D) ≫
        (alternatingFaceMapComplex C).obj A ◁ alexanderWhitney B D := by
  ext n : 1
  simp only [HomologicalComplex.comp_f]
  rw [alexanderWhitney_f_eq_sum (A ⊗ B) D, alexanderWhitney_f_eq_sum A (B ⊗ D)]
  -- The summands are typed by the degreewise objects `A _⦋n⦌ ⊗ B _⦋n⦌`, which agree with the
  -- terms of the alternating face map complexes only up to unfolding, so the sums are
  -- distributed by `Eq.trans` rather than by rewriting.
  calc _ = ∑ pc ∈ Finset.antidiagonal n, ∑ ab ∈ Finset.antidiagonal pc.1,
          (α_ (A _⦋n⦌) (B _⦋n⦌) (D _⦋n⦌)).hom ≫ alexanderWhitneyTerm₃ A B D n ab.1 ab.2 pc.2 :=
        (Preadditive.sum_comp _ _ _).trans (Finset.sum_congr rfl fun pc hpc ↦
          alexanderWhitneyTerm_whiskerRight_associator A B D n pc.1 pc.2
            (Finset.mem_antidiagonal.mp hpc))
    _ = ∑ am ∈ Finset.antidiagonal n, ∑ bc ∈ Finset.antidiagonal am.2,
          (α_ (A _⦋n⦌) (B _⦋n⦌) (D _⦋n⦌)).hom ≫ alexanderWhitneyTerm₃ A B D n am.1 bc.1 bc.2 := by
        rw [Finset.sum_sigma', Finset.sum_sigma']
        -- reindex the tridegrees: `((a + b, c), (a, b)) ↦ ((a, b + c), (b, c))`
        apply Finset.sum_nbij' (fun ⟨⟨_, c⟩, ⟨a, b⟩⟩ ↦ ⟨(a, b + c), (b, c)⟩)
          (fun ⟨⟨a, _⟩, ⟨b, c⟩⟩ ↦ ⟨(a + b, c), (a, b)⟩) <;> aesop (add simp [add_assoc])
    _ = _ := by
        symm
        refine (congrArg _ (Preadditive.sum_comp _ _ _)).trans
          ((Preadditive.comp_sum _ _ _).trans (Finset.sum_congr rfl fun am ham ↦ ?_))
        exact (congrArg (_ ≫ ·) (alexanderWhitneyTerm_whiskerLeft A B D n am.1 am.2
          (Finset.mem_antidiagonal.mp ham))).trans (Preadditive.comp_sum _ _ _)

end Coassociativity

section Counit

/-- The counit of the Alexander–Whitney map: the identity of `𝟙_ C` in degree zero, from the
alternating face map complex of the constant simplicial object `𝟙_ (SimplicialObject C)` to the
tensor unit of chain complexes.  It is a chain map because the zeroth differential of a constant
simplicial object is the difference of two identities. -/
private def alexanderWhitneyCounit :
    (alternatingFaceMapComplex C).obj (𝟙_ (SimplicialObject C)) ⟶ 𝟙_ (ChainComplex C ℕ) :=
  HomologicalComplex.mkHomToSingle (𝟙 (𝟙_ C)) fun i hi ↦ by
    obtain rfl : i = 1 := by simpa using hi.symm
    simp [Fin.sum_univ_two, SimplicialObject.δ]

private lemma alexanderWhitneyCounit_f_zero :
    (alexanderWhitneyCounit (C := C)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ C)).inv :=
  (HomologicalComplex.mkHomToSingle_f _ _).trans (Category.id_comp _)

private lemma alexanderWhitneyCounit_f_eq_zero {p : ℕ} (hp : p ≠ 0) :
    (alexanderWhitneyCounit (C := C)).f p = 0 :=
  (HomologicalComplex.isZero_single_obj_X _ _ _ p hp).eq_of_tgt _ _

/-- Only the summand of bidegree `(0, n)` of the Alexander–Whitney map of `𝟙_ _` and `A` survives
the counit, and it is the inclusion of `𝟙_ C ⊗ Aₙ`. -/
private lemma alexanderWhitneyTerm_counit_whiskerRight (n p q : ℕ) (h : p + q = n) :
    alexanderWhitneyTerm (𝟙_ _) A n p q ≫
        (alexanderWhitneyCounit ▷ (alternatingFaceMapComplex C).obj A).f n =
      if p = 0 then
        ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ C)).inv ▷ A _⦋n⦌) ≫
          ιTensorObj (𝟙_ (ChainComplex C ℕ)) ((alternatingFaceMapComplex C).obj A) 0 n n
            (zero_add n)
      else 0 := by
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ _ h, Category.assoc, ι_whiskerRight]
  split_ifs with hp
  · subst hp
    obtain rfl : q = n := by omega
    simp only [alexanderWhitneyCounit_f_zero, Monoidal.tensorUnit_map,
      MathlibExt.DGSource.SimplexCategory.subinterval_zero_eq_id, op_id, CategoryTheory.Functor.map_id]
    dsimp only [alternatingFaceMapComplex_obj_X, Monoidal.tensorUnit_obj]
    simp only [id_tensorHom_id, Category.id_comp]
  · rw [alexanderWhitneyCounit_f_eq_zero hp, MonoidalPreadditive.zero_whiskerRight, zero_comp,
      comp_zero]

/-- Only the summand of bidegree `(n, 0)` of the Alexander–Whitney map of `A` and `𝟙_ _` survives
the counit, and it is the inclusion of `Aₙ ⊗ 𝟙_ C`. -/
private lemma alexanderWhitneyTerm_whiskerLeft_counit (n p q : ℕ) (h : p + q = n) :
    alexanderWhitneyTerm A (𝟙_ _) n p q ≫
        ((alternatingFaceMapComplex C).obj A ◁ alexanderWhitneyCounit).f n =
      if q = 0 then
        (A _⦋n⦌ ◁ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ C)).inv) ≫
          ιTensorObj ((alternatingFaceMapComplex C).obj A) (𝟙_ (ChainComplex C ℕ)) n 0 n
            (add_zero n)
      else 0 := by
  rw [alexanderWhitneyTerm_of_eq _ _ _ _ _ h, Category.assoc, ι_whiskerLeft]
  split_ifs with hq
  · subst hq
    obtain rfl : p = n := by omega
    simp only [alexanderWhitneyCounit_f_zero, Monoidal.tensorUnit_map,
      MathlibExt.DGSource.SimplexCategory.subinterval_zero_eq_id, op_id, CategoryTheory.Functor.map_id]
    dsimp only [alternatingFaceMapComplex_obj_X, Monoidal.tensorUnit_obj]
    simp only [id_tensorHom_id, Category.id_comp]
  · rw [alexanderWhitneyCounit_f_eq_zero hq, MonoidalPreadditive.whiskerLeft_zero, zero_comp,
      comp_zero]

/-- Left counitality of the Alexander–Whitney map. -/
private lemma alexanderWhitney_counit_whiskerRight :
    (λ_ ((alternatingFaceMapComplex C).obj A)).inv =
      (alternatingFaceMapComplex C).map (λ_ A).inv ≫ alexanderWhitney (𝟙_ _) A ≫
        alexanderWhitneyCounit ▷ (alternatingFaceMapComplex C).obj A := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, alexanderWhitney_f_eq_sum,
    leftUnitor_inv_f, leftUnitor'_inv]
  dsimp only [alternatingFaceMapComplex_obj_X, Monoidal.tensorObj_obj, Monoidal.tensorUnit_obj]
  rw [alternatingFaceMapComplex_map_f, Monoidal.leftUnitor_inv_app]
  congr 1
  refine Eq.symm ((Preadditive.sum_comp _ _ _).trans ?_)
  rw [Finset.sum_eq_single (0, n) (fun pq hpq hne ↦ ?_) (by simp)]
  · exact (alexanderWhitneyTerm_counit_whiskerRight A n 0 n (zero_add n)).trans (ite_eq_left rfl)
  · obtain ⟨p, q⟩ := pq
    have h : p + q = n := Finset.mem_antidiagonal.mp hpq
    have hp : p ≠ 0 := by rintro rfl; exact hne (by simp_all)
    exact (alexanderWhitneyTerm_counit_whiskerRight A n p q h).trans (ite_eq_right hp)

/-- Right counitality of the Alexander–Whitney map. -/
private lemma alexanderWhitney_whiskerLeft_counit :
    (ρ_ ((alternatingFaceMapComplex C).obj A)).inv =
      (alternatingFaceMapComplex C).map (ρ_ A).inv ≫ alexanderWhitney A (𝟙_ _) ≫
        (alternatingFaceMapComplex C).obj A ◁ alexanderWhitneyCounit := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, alexanderWhitney_f_eq_sum,
    rightUnitor_inv_f, rightUnitor'_inv]
  dsimp only [alternatingFaceMapComplex_obj_X, Monoidal.tensorObj_obj, Monoidal.tensorUnit_obj]
  rw [alternatingFaceMapComplex_map_f, Monoidal.rightUnitor_inv_app]
  congr 1
  refine Eq.symm ((Preadditive.sum_comp _ _ _).trans ?_)
  rw [Finset.sum_eq_single (n, 0) (fun pq hpq hne ↦ ?_) (by simp)]
  · exact (alexanderWhitneyTerm_whiskerLeft_counit A n n 0 (add_zero n)).trans (ite_eq_left rfl)
  · obtain ⟨p, q⟩ := pq
    have h : p + q = n := Finset.mem_antidiagonal.mp hpq
    have hq : q ≠ 0 := by rintro rfl; exact hne (by simp_all)
    exact (alexanderWhitneyTerm_whiskerLeft_counit A n p q h).trans (ite_eq_right hq)

end Counit

/-- **The Alexander–Whitney oplax monoidal structure** on the alternating face map complex
functor: the comultiplication is the Alexander–Whitney map
(`CategoryTheory.SimplicialObject.alternatingFaceMapComplex_δ`), and the counit is the identity
of `𝟙_ C` in degree zero (`CategoryTheory.SimplicialObject.alternatingFaceMapComplex_η_f_zero`).
Coassociativity is `CategoryTheory.SimplicialObject.alexanderWhitney_coassoc`. -/
@[no_expose]
instance alternatingFaceMapComplexOplaxMonoidal :
    (alternatingFaceMapComplex C).OplaxMonoidal where
  η := alexanderWhitneyCounit
  δ := alexanderWhitney
  δ_natural_left f B := by
    simpa using (alexanderWhitney_naturality f (𝟙 B)).symm
  δ_natural_right A g := by
    simpa using (alexanderWhitney_naturality (𝟙 A) g).symm
  oplax_associativity := alexanderWhitney_coassoc
  oplax_left_unitality := alexanderWhitney_counit_whiskerRight
  oplax_right_unitality := alexanderWhitney_whiskerLeft_counit

/-- The comultiplication of the alternating face map complex functor is the Alexander–Whitney
map. -/
@[simp]
lemma alternatingFaceMapComplex_δ :
    Functor.OplaxMonoidal.δ (alternatingFaceMapComplex C) A B = alexanderWhitney A B :=
  (rfl)

/-- The counit of the alternating face map complex functor is the identity of `𝟙_ C` in degree
zero; in positive degrees its target is zero. -/
@[simp]
lemma alternatingFaceMapComplex_η_f_zero :
    (Functor.OplaxMonoidal.η (alternatingFaceMapComplex C)).f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 (𝟙_ C)).inv :=
  alexanderWhitneyCounit_f_zero (C := C)

end CategoryTheory.SimplicialObject
