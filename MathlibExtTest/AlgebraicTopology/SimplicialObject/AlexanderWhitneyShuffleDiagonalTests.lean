/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialObject.AlexanderWhitney.ChainMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialAlexanderWhitney
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.EilenbergZilber.Shuffle
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.ChainMap
public import MathlibExt.AlgebraicTopology.SimplicialObject.BisimplicialEilenbergZilber.Normalization
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Concrete Alexander–Whitney, shuffle and diagonal computations

The cut inclusions of the Alexander–Whitney map are computed on `⦋1⦌` and `⦋2⦌`, the front
and back faces are evaluated on the top simplices of `Δ[1]` and `Δ[2]`, the degree-one
Alexander–Whitney component and the `(1, 1)` Eilenberg–Zilber shuffle map are identified with
the classical face and degeneracy formulas, and the degree-one bisimplicial component is split
into its outer and inner faces. With integer coefficients, the two degree-one terms are evaluated
on the tensor square of the edge of `Δ[1]`; on the external product `Δ[1] ⊠ Δ[1]` the diagonal
faces act on both coordinates and the bisimplicial maps on one. There are `(p + q).choose p`
shuffles of type `(p, q)`. On the free bisimplicial abelian group of `Δ[1] ⊠ Δ[1]`, the
Eilenberg–Zilber map sends the top generator to the nonzero chain `[(s₁, s₀)] - [(s₀, s₁)]`, whose
diagonal boundary is computed, and the Eilenberg–Zilber chain map, its differential identity and the
degree-zero normalization projector are instantiated there. The bisimplicial total complex only
needs finite coproducts.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite Simplicial

noncomputable section

universe v u

namespace AlgebraicTopology.AlexanderWhitneyShuffleDiagonalTests

open AlexanderWhitney

/-! ### The cut inclusions -/

/-- The front edge of the `(1, 1)` cut of `⦋2⦌` is the edge `[0, 1]`, the face skipping `2`. -/
theorem frontInclusion_one_one : frontInclusion 1 1 2 rfl = SimplexCategory.δ 2 := by
  ext i
  fin_cases i <;> rfl

/-- The back edge of the `(1, 1)` cut of `⦋2⦌` is the edge `[1, 2]`, the face skipping `0`. -/
theorem backInclusion_one_one : backInclusion 1 1 2 rfl = SimplexCategory.δ 0 := by
  ext i
  fin_cases i <;> rfl

/-- The two edges of the `(1, 1)` cut share exactly the middle vertex. -/
example : (frontInclusion 1 1 2 rfl).toOrderHom 1 = 1 ∧
    (backInclusion 1 1 2 rfl).toOrderHom 0 = 1 ∧
    (frontInclusion 1 1 2 rfl).toOrderHom 0 ≠ (backInclusion 1 1 2 rfl).toOrderHom 1 := by
  decide

/-- The front and back edges of the `(1, 1)` cut are different maps. -/
example : frontInclusion 1 1 2 rfl ≠ backInclusion 1 1 2 rfl := by
  rw [frontInclusion_one_one, backInclusion_one_one]
  intro h
  have := congrArg (fun f : ⦋1⦌ ⟶ ⦋2⦌ => f.toOrderHom 0) h
  exact absurd this (by decide)

/-- In degree one the cut at `0` takes the vertex `0` in front and the whole edge in back. -/
theorem frontInclusion_zero_one : frontInclusion 0 1 1 rfl = SimplexCategory.δ 1 := by
  ext i
  fin_cases i
  rfl

theorem backInclusion_zero_one : backInclusion 0 1 1 rfl = 𝟙 ⦋1⦌ := by
  ext i
  fin_cases i <;> rfl

/-- In degree one the cut at `1` takes the whole edge in front and the vertex `1` in back. -/
theorem frontInclusion_one_zero : frontInclusion 1 0 1 rfl = 𝟙 ⦋1⦌ := by
  ext i
  fin_cases i <;> rfl

theorem backInclusion_one_zero : backInclusion 1 0 1 rfl = SimplexCategory.δ 0 := by
  ext i
  fin_cases i
  rfl

/-! ### Faces of standard simplices -/

/-- The front and back faces of the edge of `Δ[1]` are its two distinct endpoints. -/
example :
    SSet.stdSimplex.obj₀Equiv
        (frontFace (Δ[1] : SSet.{0}) (show 0 + 1 = 1 from rfl)
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))) = 0 ∧
      SSet.stdSimplex.obj₀Equiv
        (backFace (Δ[1] : SSet.{0}) (show 1 + 0 = 1 from rfl)
          (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))) = 1 :=
  ⟨rfl, rfl⟩

/-- The `(1, 1)` front and back faces of the top simplex of `Δ[2]` are the edges `[0, 1]` and
`[1, 2]`. -/
example :
    (∀ i : Fin 2, (frontFace (Δ[2] : SSet.{0}) (show 1 + 1 = 2 from rfl)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋2⦌))) i = i.castSucc) ∧
      (∀ i : Fin 2, (backFace (Δ[2] : SSet.{0}) (show 1 + 1 = 2 from rfl)
        (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋2⦌))) i = i.succ) :=
  ⟨fun i => by fin_cases i <;> rfl, fun i => by fin_cases i <;> rfl⟩

/-! ### The degree-one Alexander–Whitney component -/

section Component

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ Z : C, ((curriedTensor C).obj Z).Additive]
  (X Y : SimplicialObject C)
  [HomologicalComplex.HasTensor ((alternatingFaceMapComplex C).obj X)
    ((alternatingFaceMapComplex C).obj Y)]

/-- In degree one the Alexander–Whitney map is `x ⊗ y ↦ d₁ x ⊗ y + x ⊗ d₀ y`. -/
theorem alternatingComponent_one :
    alternatingComponent X Y 1 =
      (X.δ 1 ⊗ₘ 𝟙 (Y.obj (op ⦋1⦌))) ≫
          HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex C).obj X)
            ((alternatingFaceMapComplex C).obj Y) 0 1 1 rfl +
        (𝟙 (X.obj (op ⦋1⦌)) ⊗ₘ Y.δ 0) ≫
          HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex C).obj X)
            ((alternatingFaceMapComplex C).obj Y) 1 0 1 rfl := by
  rw [alternatingComponent_eq_sum, Fin.sum_univ_two]
  congr 1
  · change (X.map (frontInclusion 0 1 1 rfl).op ⊗ₘ Y.map (backInclusion 0 1 1 rfl).op) ≫
      HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex C).obj X)
        ((alternatingFaceMapComplex C).obj Y) 0 1 1 rfl = _
    rw [frontInclusion_zero_one, backInclusion_zero_one, op_id, Y.map_id]
    rfl
  · change (X.map (frontInclusion 1 0 1 rfl).op ⊗ₘ Y.map (backInclusion 1 0 1 rfl).op) ≫
      HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex C).obj X)
        ((alternatingFaceMapComplex C).obj Y) 1 0 1 rfl = _
    rw [frontInclusion_one_zero, backInclusion_one_zero, op_id, X.map_id]
    rfl

end Component

/-- The Alexander–Whitney chain map exists for simplicial abelian groups. -/
example (X Y : SimplicialObject (ModuleCat.{0} ℤ)) :
    (alternatingMap X Y).f 1 =
      (X.δ 1 ⊗ₘ 𝟙 (Y.obj (op ⦋1⦌))) ≫
          HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex _).obj X)
            ((alternatingFaceMapComplex _).obj Y) 0 1 1 rfl +
        (𝟙 (X.obj (op ⦋1⦌)) ⊗ₘ Y.δ 0) ≫
          HomologicalComplex.ιTensorObj ((alternatingFaceMapComplex _).obj X)
            ((alternatingFaceMapComplex _).obj Y) 1 0 1 rfl :=
  alternatingComponent_one X Y

/-! ### The `(1, 1)` shuffles and the Eilenberg–Zilber map in bidegree `(1, 1)` -/

namespace ShuffleOneOne

open EilenbergZilber

/-- The `(1, 1)` shuffle that keeps the first block first: the identity permutation. -/
def first : Shuffle 1 1 :=
  ⟨1, Subsingleton.strictMono _, Subsingleton.strictMono _⟩

/-- The `(1, 1)` shuffle that puts the second block first: the transposition. -/
def second : Shuffle 1 1 :=
  ⟨Equiv.swap 0 1, Subsingleton.strictMono _, Subsingleton.strictMono _⟩

/-- `(1, 1)` shuffles are compared through their permutations. -/
instance : DecidableEq (Shuffle 1 1) := fun s t =>
  decidable_of_iff (s.perm = t.perm) ⟨Shuffle.ext, fun h => h ▸ rfl⟩

theorem first_ne_second : first ≠ second := by
  intro h
  have := congrArg (fun s : Shuffle 1 1 => s.perm 0) h
  exact absurd this (by decide)

/-- These are the only `(1, 1)` shuffles. -/
theorem eq_first_or_second (s : Shuffle 1 1) : s = first ∨ s = second := by
  have hperm : ∀ σ : Equiv.Perm (Fin 2), σ = 1 ∨ σ = Equiv.swap 0 1 := by decide
  rcases hperm s.perm with h | h
  · exact Or.inl (Shuffle.ext h)
  · exact Or.inr (Shuffle.ext h)

theorem univ_eq : (Finset.univ : Finset (Shuffle 1 1)) = {first, second} := by
  ext s
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact eq_first_or_second s

/-- There are `choose 2 1 = 2` shuffles of type `(1, 1)`. -/
theorem card : Fintype.card (Shuffle 1 1) = 2 := by
  rw [← Finset.card_univ, univ_eq, Finset.card_pair first_ne_second]

theorem shuffleSignZ_first : shuffleSignZ first = 1 := by
  simp [shuffleSignZ, shuffleSign, first]

theorem shuffleSignZ_second : shuffleSignZ second = -1 := by
  simp [shuffleSignZ, shuffleSign, second, Equiv.Perm.sign_swap (show (0 : Fin 2) ≠ 1 by decide)]

/-- The identity shuffle collapses the last edge on the left and the first edge on the right. -/
theorem leftHom_first : first.leftHom = SimplexCategory.σ 1 := by
  ext k
  fin_cases k <;> decide

theorem rightHom_first : first.rightHom = SimplexCategory.σ 0 := by
  ext k
  fin_cases k <;> decide

theorem leftHom_second : second.leftHom = SimplexCategory.σ 0 := by
  ext k
  fin_cases k <;> decide

theorem rightHom_second : second.rightHom = SimplexCategory.σ 1 := by
  ext k
  fin_cases k <;> decide

end ShuffleOneOne

section Shuffle

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  (X Y : SimplicialObject C)

/-- In bidegree `(1, 1)` the shuffle map is `x ⊗ y ↦ s₁ x ⊗ s₀ y - s₀ x ⊗ s₁ y`. -/
theorem shuffleBidegree_one_one :
    EilenbergZilber.shuffleBidegree X Y 1 1 = (X.σ 1 ⊗ₘ Y.σ 0) - (X.σ 0 ⊗ₘ Y.σ 1) := by
  rw [EilenbergZilber.shuffleBidegree, ShuffleOneOne.univ_eq,
    Finset.sum_pair ShuffleOneOne.first_ne_second]
  simp only [EilenbergZilber.shuffleSummand, ShuffleOneOne.shuffleSignZ_first,
    ShuffleOneOne.shuffleSignZ_second, ShuffleOneOne.leftHom_first, ShuffleOneOne.rightHom_first,
    ShuffleOneOne.leftHom_second, ShuffleOneOne.rightHom_second, one_smul, neg_smul]
  exact (sub_eq_add_neg _ _).symm

end Shuffle

/-! ### The degree-one bisimplicial Alexander–Whitney component -/

section Bisimplicial

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteCoproducts A]
  (B : SimplicialObject (SimplicialObject A))

/-- The face map of a cut is the bisimplicial map of its front and back inclusions. -/
example (p q n : ℕ) (h : p + q = n) :
    BisimplicialAlexanderWhitney.faceToBidegreeOfEq B p q n h =
      Bisimplicial.map B (frontInclusion p q n h) (backInclusion p q n h) :=
  rfl

/-- In degree one the bisimplicial Alexander–Whitney component applies the outer face `d₁` into
bidegree `(0, 1)` and the inner face `d₀` into bidegree `(1, 0)`. -/
theorem component_one :
    BisimplicialAlexanderWhitney.component B 1 =
      (B.δ 1).app (op ⦋1⦌) ≫ BisimplicialAlexanderWhitney.totalιOfEq B 0 1 1 rfl +
        (B.obj (op ⦋1⦌)).δ 0 ≫ BisimplicialAlexanderWhitney.totalιOfEq B 1 0 1 rfl := by
  rw [BisimplicialAlexanderWhitney.component_eq_sum, Fin.sum_univ_two]
  congr 1
  · change Bisimplicial.map B (frontInclusion 0 1 1 rfl) (backInclusion 0 1 1 rfl) ≫
      BisimplicialAlexanderWhitney.totalιOfEq B 0 1 1 rfl = _
    rw [frontInclusion_zero_one, backInclusion_zero_one, Bisimplicial.map_delta_id]
  · change Bisimplicial.map B (frontInclusion 1 0 1 rfl) (backInclusion 1 0 1 rfl) ≫
      BisimplicialAlexanderWhitney.totalιOfEq B 1 0 1 rfl = _
    rw [frontInclusion_one_zero, backInclusion_one_zero, Bisimplicial.map_id_delta]

end Bisimplicial

/-! ### Integer coefficients on the edge of `Δ[1]` -/

section FreeEdge

/-- The free simplicial abelian group on the standard `1`-simplex. -/
abbrev freeEdge : SimplicialObject (ModuleCat.{0} ℤ) :=
  ((SimplicialObject.whiskering _ _).obj (ModuleCat.free ℤ)).obj (Δ[1] : SSet.{0})

/-- The basis element of the edge `[0, 1]`. -/
abbrev edge : freeEdge.obj (op ⦋1⦌) := ModuleCat.freeMk (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌))

/-- The basis element of the vertex `i`. -/
abbrev vertex (i : Fin 2) : freeEdge.obj (op ⦋0⦌) :=
  ModuleCat.freeMk (SSet.stdSimplex.obj₀Equiv.symm i)

theorem δ_one_edge : freeEdge.δ 1 edge = vertex 0 := by
  change (ModuleCat.free ℤ).map _ (ModuleCat.freeMk _) = _
  rw [ModuleCat.free_map_apply]
  congr 1
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem δ_zero_edge : freeEdge.δ 0 edge = vertex 1 := by
  change (ModuleCat.free ℤ).map _ (ModuleCat.freeMk _) = _
  rw [ModuleCat.free_map_apply]
  congr 1
  apply SSet.stdSimplex.obj₀Equiv.injective
  rw [Equiv.apply_symm_apply]
  rfl

/-- The two endpoints of the edge are different basis elements. -/
theorem vertex_zero_ne_one : vertex 0 ≠ vertex 1 := by
  intro h
  have := (Finsupp.single_left_injective (one_ne_zero (α := ℤ))) h
  exact absurd (SSet.stdSimplex.obj₀Equiv.symm.injective this) (by decide)

/-- The bidegree `(0, 1)` term of `alternatingComponent_one` sends `[0, 1] ⊗ [0, 1]` to
`[0] ⊗ [0, 1]`. -/
example : (freeEdge.δ 1 ⊗ₘ 𝟙 (freeEdge.obj (op ⦋1⦌))) (edge ⊗ₜ[ℤ] edge) =
    vertex 0 ⊗ₜ[ℤ] edge := by
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul, δ_one_edge]
  rfl

/-- The bidegree `(1, 0)` term of `alternatingComponent_one` sends `[0, 1] ⊗ [0, 1]` to
`[0, 1] ⊗ [1]`. -/
example : (𝟙 (freeEdge.obj (op ⦋1⦌)) ⊗ₘ freeEdge.δ 0) (edge ⊗ₜ[ℤ] edge) =
    edge ⊗ₜ[ℤ] vertex 1 := by
  rw [ModuleCat.MonoidalCategory.tensorHom_tmul, δ_zero_edge]
  rfl

end FreeEdge

/-! ### The diagonal of an external product -/

section ExternalProduct

/-- The external product of two simplicial sets: its `(p, q)`-simplices are the pairs of a
`p`-simplex and a `q`-simplex. -/
abbrev boxProduct (X Y : SSet.{0}) : SimplicialObject SSet.{0} :=
  Functor.curry.obj (X.prod Y ⋙ MonoidalCategory.tensor (Type 0))

/-- The edge of `Δ[1]`. -/
abbrev e₁ : (Δ[1] : SSet.{0}).obj (op ⦋1⦌) := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)

/-- The vertex `i` of `Δ[1]`. -/
abbrev v₁ (i : Fin 2) : (Δ[1] : SSet.{0}).obj (op ⦋0⦌) := SSet.stdSimplex.obj₀Equiv.symm i

/-- A diagonal face of `Δ[1] ⊠ Δ[1]` acts on both coordinates. -/
example : ((SimplicialObject.diagonalFunctor _).obj (boxProduct Δ[1] Δ[1])).δ (n := 0) 0
      ((e₁, e₁) : Δ[1] _⦋1⦌ × Δ[1] _⦋1⦌) = ((v₁ 1, v₁ 1) : Δ[1] _⦋0⦌ × Δ[1] _⦋0⦌) := by
  refine Prod.ext ?_ ?_ <;>
    exact SSet.stdSimplex.ext _ _ fun i => by fin_cases i; rfl

example : ((SimplicialObject.diagonalFunctor _).obj (boxProduct Δ[1] Δ[1])).δ (n := 0) 1
      ((e₁, e₁) : Δ[1] _⦋1⦌ × Δ[1] _⦋1⦌) = ((v₁ 0, v₁ 0) : Δ[1] _⦋0⦌ × Δ[1] _⦋0⦌) := by
  refine Prod.ext ?_ ?_ <;>
    exact SSet.stdSimplex.ext _ _ fun i => by fin_cases i; rfl

/-- The outer face of the bisimplicial map acts on the first coordinate only. -/
example : Bisimplicial.map (boxProduct Δ[1] Δ[1]) (SimplexCategory.δ (n := 0) 1) (𝟙 ⦋1⦌)
      ((e₁, e₁) : Δ[1] _⦋1⦌ × Δ[1] _⦋1⦌) = ((v₁ 0, e₁) : Δ[1] _⦋0⦌ × Δ[1] _⦋1⦌) := by
  refine Prod.ext ?_ ?_
  · exact SSet.stdSimplex.ext _ _ fun i => by fin_cases i; rfl
  · exact SSet.stdSimplex.ext _ _ fun i => by fin_cases i <;> rfl

/-- The inner face of the bisimplicial map acts on the second coordinate only. -/
example : Bisimplicial.map (boxProduct Δ[1] Δ[1]) (𝟙 ⦋1⦌) (SimplexCategory.δ (n := 0) 0)
      ((e₁, e₁) : Δ[1] _⦋1⦌ × Δ[1] _⦋1⦌) = ((e₁, v₁ 1) : Δ[1] _⦋1⦌ × Δ[1] _⦋0⦌) := by
  refine Prod.ext ?_ ?_
  · exact SSet.stdSimplex.ext _ _ fun i => by fin_cases i <;> rfl
  · exact SSet.stdSimplex.ext _ _ fun i => by fin_cases i; rfl

end ExternalProduct

/-! ### The number of shuffles -/

/-- A `(p, q)` shuffle is determined by the positions of its first block, so there are
`(p + q).choose p` of them. -/
theorem card_shuffle (p q : ℕ) :
    Nat.card (EilenbergZilber.Shuffle p q) = (p + q).choose p := by
  rw [Nat.card_congr (EilenbergZilber.Shuffle.equivLeftPositions (p := p) (q := q)),
    Set.powersetCard.card]
  simp

example : Nat.card (EilenbergZilber.Shuffle 2 1) = 3 := by
  rw [card_shuffle]
  rfl

/-! ### The Eilenberg–Zilber map on the free bisimplicial abelian group of `Δ[1] ⊠ Δ[1]` -/

section FreeBisimplex

open EilenbergZilber

set_option backward.isDefEq.respectTransparency false

/-- The free bisimplicial abelian group on `Δ[p] ⊠ Δ[q]`: in bidegree `(r, t)` it is free on the
pairs of maps `⦋r⦌ ⟶ ⦋p⦌` and `⦋t⦌ ⟶ ⦋q⦌`. -/
abbrev freeBisimplex (p q : ℕ) : SimplicialObject (SimplicialObject (ModuleCat.{0} ℤ)) :=
  yoneda.obj ⦋p⦌ ⋙ Functor.const SimplexCategoryᵒᵖ ⋙
    (curriedTensor (SimplexCategoryᵒᵖ ⥤ Type)).flip.obj (yoneda.obj ⦋q⦌) ⋙
    (SimplicialObject.whiskering (Type) (ModuleCat ℤ)).obj (ModuleCat.free ℤ)

theorem module_sum_apply {M N : ModuleCat.{0} ℤ} {I : Type} [Fintype I]
    (maps : I → (M ⟶ N)) (x : M) :
    (∑ i, maps i) x = ∑ i, maps i x := by
  change (∑ i, maps i).hom x = _
  rw [ModuleCat.hom_sum]
  exact LinearMap.sum_apply _ _ _

theorem module_map_sub {M N : ModuleCat.{0} ℤ} (f : M ⟶ N) (x y : M) :
    f (x - y) = f x - f y :=
  f.hom.map_sub x y

theorem module_zsmul_apply {M N : ModuleCat.{0} ℤ} (k : ℤ) (f : M ⟶ N) (x : M) :
    (k • f) x = k • f x := by
  change (k • f).hom x = _
  rw [ModuleCat.hom_zsmul]
  rfl

/-- The bisimplicial maps act on generators by precomposition. -/
theorem map_freeMk (p q r t n m : ℕ) (α : ⦋n⦌ ⟶ ⦋r⦌) (β : ⦋m⦌ ⟶ ⦋t⦌)
    (f : ⦋r⦌ ⟶ ⦋p⦌) (g : ⦋t⦌ ⟶ ⦋q⦌) :
    Bisimplicial.map (freeBisimplex p q) α β (ModuleCat.freeMk (f, g)) =
      ModuleCat.freeMk (α ≫ f, β ≫ g) := by
  change ((ModuleCat.free ℤ).map (↾fun z => (z.1, β ≫ z.2)))
      (((ModuleCat.free ℤ).map (↾fun z => (α ≫ z.1, z.2))) (ModuleCat.freeMk (f, g))) = _
  simp only [ModuleCat.free_map_apply]
  rfl

theorem shuffleSummand_freeMk {p q r t : ℕ} (s : Shuffle r t) (f : ⦋r⦌ ⟶ ⦋p⦌)
    (g : ⦋t⦌ ⟶ ⦋q⦌) :
    BisimplicialEilenbergZilber.shuffleSummand (freeBisimplex p q) s (ModuleCat.freeMk (f, g)) =
      shuffleSignZ s • ModuleCat.freeMk (s.leftHom ≫ f, s.rightHom ≫ g) := by
  change shuffleSignZ s •
    (Bisimplicial.map (freeBisimplex p q) s.leftHom s.rightHom (ModuleCat.freeMk (f, g))) = _
  rw [map_freeMk]

/-- The Eilenberg–Zilber map sends the generator `(𝟙, 𝟙)` of bidegree `(1, 1)` to
`[(s₁, s₀)] - [(s₀, s₁)]`. -/
theorem shuffleBidegree_freeMk_one_one :
    BisimplicialEilenbergZilber.shuffleBidegree (freeBisimplex 1 1) 1 1
        (ModuleCat.freeMk (𝟙 ⦋1⦌, 𝟙 ⦋1⦌)) =
      ModuleCat.freeMk (SimplexCategory.σ (1 : Fin 2), SimplexCategory.σ (0 : Fin 2)) -
        ModuleCat.freeMk (SimplexCategory.σ (0 : Fin 2), SimplexCategory.σ (1 : Fin 2)) := by
  rw [BisimplicialEilenbergZilber.shuffleBidegree, ShuffleOneOne.univ_eq,
    Finset.sum_pair ShuffleOneOne.first_ne_second]
  change
    BisimplicialEilenbergZilber.shuffleSummand (freeBisimplex 1 1) ShuffleOneOne.first
        (ModuleCat.freeMk (𝟙 ⦋1⦌, 𝟙 ⦋1⦌)) +
      BisimplicialEilenbergZilber.shuffleSummand (freeBisimplex 1 1) ShuffleOneOne.second
        (ModuleCat.freeMk (𝟙 ⦋1⦌, 𝟙 ⦋1⦌)) = _
  rw [shuffleSummand_freeMk, shuffleSummand_freeMk, ShuffleOneOne.shuffleSignZ_first,
    ShuffleOneOne.shuffleSignZ_second, ShuffleOneOne.leftHom_first, ShuffleOneOne.rightHom_first,
    ShuffleOneOne.leftHom_second, ShuffleOneOne.rightHom_second, one_smul, neg_smul,
    ← sub_eq_add_neg]
  simp only [Category.comp_id, one_smul]

/-- That chain is not zero. -/
theorem shuffleBidegree_freeMk_one_one_ne_zero :
    BisimplicialEilenbergZilber.shuffleBidegree (freeBisimplex 1 1) 1 1
        (ModuleCat.freeMk (𝟙 ⦋1⦌, 𝟙 ⦋1⦌)) ≠ 0 := by
  rw [shuffleBidegree_freeMk_one_one]
  intro h
  have hcoeff := congrArg
    (fun z : (⦋2⦌ ⟶ ⦋1⦌) × (⦋2⦌ ⟶ ⦋1⦌) →₀ ℤ =>
      z (SimplexCategory.σ (1 : Fin 2), SimplexCategory.σ (0 : Fin 2))) h
  have hne : (SimplexCategory.σ (0 : Fin 2), SimplexCategory.σ (1 : Fin 2)) ≠
      (SimplexCategory.σ (1 : Fin 2), SimplexCategory.σ (0 : Fin 2)) := by decide
  change
    ((Finsupp.single (SimplexCategory.σ (1 : Fin 2), SimplexCategory.σ (0 : Fin 2)) (1 : ℤ) -
      Finsupp.single (SimplexCategory.σ (0 : Fin 2), SimplexCategory.σ (1 : Fin 2)) 1) :
        ((⦋2⦌ ⟶ ⦋1⦌) × (⦋2⦌ ⟶ ⦋1⦌)) →₀ ℤ)
          (SimplexCategory.σ (1 : Fin 2), SimplexCategory.σ (0 : Fin 2)) = 0 at hcoeff
  simp [hne] at hcoeff

theorem diagonal_δ_freeMk {p q n : ℕ} (i : Fin (n + 2)) (f : ⦋n + 1⦌ ⟶ ⦋p⦌)
    (g : ⦋n + 1⦌ ⟶ ⦋q⦌) :
    ((SimplicialObject.diagonalFunctor (ModuleCat ℤ)).obj (freeBisimplex p q)).δ i
        (ModuleCat.freeMk (f, g)) =
      ModuleCat.freeMk (SimplexCategory.δ i ≫ f, SimplexCategory.δ i ≫ g) := by
  change ((SimplicialObject.diagonalFunctor (ModuleCat ℤ)).obj (freeBisimplex p q)).map
      (SimplexCategory.δ i).op (ModuleCat.freeMk (f, g)) = _
  rw [← Bisimplicial.map_diagonal]
  exact map_freeMk p q (n + 1) (n + 1) n n _ _ f g

theorem diagonal_objD_freeMk {p q n : ℕ} (f : ⦋n + 1⦌ ⟶ ⦋p⦌) (g : ⦋n + 1⦌ ⟶ ⦋q⦌) :
    AlternatingFaceMapComplex.objD
        ((SimplicialObject.diagonalFunctor (ModuleCat ℤ)).obj (freeBisimplex p q)) n
        (ModuleCat.freeMk (f, g)) =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.val) •
        ModuleCat.freeMk (SimplexCategory.δ i ≫ f, SimplexCategory.δ i ≫ g) := by
  unfold AlternatingFaceMapComplex.objD
  rw [module_sum_apply]
  simp only [module_zsmul_apply, diagonal_δ_freeMk]

/-- The diagonal boundary of the Eilenberg–Zilber chain `[(s₁, s₀)] - [(s₀, s₁)]`: the middle faces
cancel and four edges remain, with the vertical sign. -/
theorem objD_shuffleBidegree_freeMk_one_one :
    AlternatingFaceMapComplex.objD
      ((SimplicialObject.diagonalFunctor (ModuleCat ℤ)).obj (freeBisimplex 1 1)) 1
      (BisimplicialEilenbergZilber.shuffleBidegree (freeBisimplex 1 1) 1 1
        (ModuleCat.freeMk (𝟙 ⦋1⦌, 𝟙 ⦋1⦌))) =
    ModuleCat.freeMk (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1, 𝟙 ⦋1⦌) -
      ModuleCat.freeMk (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0, 𝟙 ⦋1⦌) -
      ModuleCat.freeMk (𝟙 ⦋1⦌, SimplexCategory.const ⦋1⦌ ⦋1⦌ 1) +
      ModuleCat.freeMk (𝟙 ⦋1⦌, SimplexCategory.const ⦋1⦌ ⦋1⦌ 0) := by
  have d0s1 : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) =
      SimplexCategory.const ⦋1⦌ ⦋1⦌ 1 := by decide
  have d1s1 : SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) = 𝟙 ⦋1⦌ := by
    decide
  have d2s1 : SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (1 : Fin 2) = 𝟙 ⦋1⦌ := by
    decide
  have d0s0 : SimplexCategory.δ (0 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) = 𝟙 ⦋1⦌ := by
    decide
  have d1s0 : SimplexCategory.δ (1 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) = 𝟙 ⦋1⦌ := by
    decide
  have d2s0 : SimplexCategory.δ (2 : Fin 3) ≫ SimplexCategory.σ (0 : Fin 2) =
      SimplexCategory.const ⦋1⦌ ⦋1⦌ 0 := by decide
  rw [shuffleBidegree_freeMk_one_one, module_map_sub, diagonal_objD_freeMk, diagonal_objD_freeMk,
    Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [d0s1, d1s1, d2s1, d0s0, d1s0, d2s0, Fin.val_zero, Fin.val_one, Fin.val_two,
    pow_zero, pow_one, one_smul, neg_smul, Int.reduceNeg, even_two, Even.neg_pow, one_pow]
  abel

/-- The Eilenberg–Zilber chain map and its differential identity on this bisimplicial object. -/
example : bisimplicialAlternatingTotalComplex (ModuleCat ℤ) (freeBisimplex 1 1) ⟶
    BisimplicialAlexanderWhitney.diagonalAlternatingComplex (freeBisimplex 1 1) :=
  BisimplicialEilenbergZilber.alternatingMap (freeBisimplex 1 1)

example : BisimplicialEilenbergZilber.component (freeBisimplex 1 1) 2 ≫
      (BisimplicialAlexanderWhitney.diagonalAlternatingComplex (freeBisimplex 1 1)).d 2 1 =
    (bisimplicialAlternatingTotalComplex (ModuleCat ℤ) (freeBisimplex 1 1)).d 2 1 ≫
      BisimplicialEilenbergZilber.component (freeBisimplex 1 1) 1 :=
  BisimplicialEilenbergZilber.component_comm (freeBisimplex 1 1) 1

/-- The normalization projector is the identity in bidegree `(0, 0)`. -/
example : BisimplicialNormalization.bidegreePInfty (freeBisimplex 1 1) 0 0 = 𝟙 _ := by
  simp [BisimplicialNormalization.bidegreePInfty]

end FreeBisimplex

/-- The bisimplicial total complex only needs finite coproducts. -/
example {A : Type u} [Category.{v} A] [Preadditive A] [HasFiniteCoproducts A]
    (B : SimplicialObject (SimplicialObject A)) (n : ℕ) :
    (BisimplicialAlexanderWhitney.diagonalAlternatingComplex B).X n ⟶
      (bisimplicialAlternatingTotalComplex A B).X n :=
  BisimplicialAlexanderWhitney.component B n

end AlgebraicTopology.AlexanderWhitneyShuffleDiagonalTests

end
