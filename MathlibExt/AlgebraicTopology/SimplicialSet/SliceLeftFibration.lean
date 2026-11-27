/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryLiftingCore
public import MathlibExt.AlgebraicTopology.SimplicialSet.HornDescent
public import MathlibExt.AlgebraicTopology.SimplicialSet.BoundaryDesc
public import MathlibExt.AlgebraicTopology.SimplicialSet.Remark33

/-!
# Left fibrations from under-slice comparisons

For an inner fibration `p : X → S` of simplicial sets and a vertex `x` of `X`,
the under-slice comparison `X_(x/) → S_(px/) ×_S X` is a left fibration.
The standard join identification describes slice simplices as successor simplices
of `X`, with their first vertex fixed, and identifies the slice projection with
face zero.

A left horn in the comparison becomes an inner horn of `p` with its missing index
shifted by one. The same pullback geometry gives left-fibration maps on the associated
left mapping spaces. Generic face-family lemmas state horn and boundary lifting for
maps with the corresponding lifting property.

See Lurie, Higher Topos Theory, Definition 2.0.0.3, Proposition 2.1.2.1,
and Lemma 2.1.3.4, and Campbell, A counterexample in quasi-category theory,
arXiv:1904.04965v3.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory Limits Opposite MorphismProperty
open scoped Simplicial
open scoped CategoryTheory.MonoidalCategory.DayFunctor

universe u

namespace SSet

variable {X Y S T E B : SSet.{u}}

/-!
## Compatible face families and lifting properties

A compatible family of faces over a bottom simplex determines a horn or boundary
lifting problem. If the map has the right lifting property against that inclusion,
there is a simplex with exactly those faces and bottom image.
-/

/--
Given compatible degree-`n` horn faces over a bottom `(n + 1)`-simplex, a map with
the corresponding horn lifting property admits a simplex having those faces and
that bottom image.
-/
theorem exists_simplex_lift_horn {n : ℕ} {i : Fin (n + 2)}
    {f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet.{u}) ⟶ X}
    (hf : horn.IsCompatible f) {p : X ⟶ Y}
    (hp : HasLiftingProperty Λ[n + 1, i].ι p)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ Y)
    (comm : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      f j hj ≫ p = stdSimplex.δ j ≫ b) :
    ∃ (φ : (Δ[n + 1] : SSet.{u}) ⟶ X),
      (∀ (j : Fin (n + 2)) (hj : j ≠ i),
        stdSimplex.δ j ≫ φ = f j hj) ∧ φ ≫ p = b := by
  have := hp
  have sq : CommSq hf.desc Λ[n + 1, i].ι p b :=
    ⟨horn.hom_ext' (fun j hj ↦ by simpa using comm j hj)⟩
  exact ⟨sq.lift, fun j hj ↦ by simp [← horn.ι_ι_assoc i j hj],
    by simp⟩

/--
The face maps obtained by restricting a map out of `∂Δ[n + 1]` form a
compatible boundary family.
-/
theorem boundary_isCompatible_of_hom {n : ℕ}
    (g : ((boundary (n + 1) : (Δ[n + 1] : SSet.{u}).Subcomplex) :
      SSet.{u}) ⟶ X) :
    boundary.IsCompatible (fun j ↦ boundary.ι j ≫ g) := by
  obtain _ | n := n
  · trivial
  · rw [boundary.isCompatible_succ_iff]
    intro j k hjk
    simp only [← Category.assoc]
    congr 1
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    rw [← cancel_mono (boundary (n + 2)).ι, Category.assoc,
      Category.assoc, boundary.ι_ι, boundary.ι_ι, Fin.pred_succ,
      Fin.castPred_castSucc, stdSimplex.δ_comp_δ (by grind)]

/--
Given a compatible family of all degree-`n` faces over a bottom `(n + 1)`-simplex,
a map with the corresponding boundary lifting property admits a simplex with those
faces and bottom image.
-/
theorem exists_simplex_lift_boundary {n : ℕ}
    {faces : Fin (n + 2) → ((Δ[n] : SSet.{u}) ⟶ X)}
    (hf : boundary.IsCompatible faces) {p : X ⟶ Y}
    (hp : HasLiftingProperty (boundary (n + 1)).ι p)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ Y)
    (comm : ∀ j : Fin (n + 2), faces j ≫ p = stdSimplex.δ j ≫ b) :
    ∃ (φ : (Δ[n + 1] : SSet.{u}) ⟶ X),
      (∀ j : Fin (n + 2), stdSimplex.δ j ≫ φ = faces j) ∧
        φ ≫ p = b := by
  have := hp
  have sq : CommSq hf.desc (boundary (n + 1)).ι p b :=
    ⟨boundary.hom_ext (fun j ↦ by
      calc boundary.ι j ≫ (hf.desc ≫ p)
          = faces j ≫ p := by
            rw [← Category.assoc, boundary.IsCompatible.ι_desc]
        _ = boundary.ι j ≫ ((boundary (n + 1)).ι ≫ b) := by
            rw [comm j, ← Category.assoc, boundary.ι_ι])⟩
  refine ⟨sq.lift, fun j ↦ ?_, sq.fac_right⟩
  calc stdSimplex.δ j ≫ sq.lift
      = boundary.ι j ≫ ((boundary (n + 1)).ι ≫ sq.lift) := by
        rw [← boundary.ι_ι, Category.assoc]
    _ = faces j := by rw [sq.fac_left, boundary.IsCompatible.ι_desc]

/--
An inner fibration has the right lifting property against each horn inclusion
whose missing index is strictly between zero and the last vertex.
-/
theorem innerFibration_hasLiftingProperty_horn {p : X ⟶ S}
    [InnerFibration p] {n : ℕ} {i : Fin (n + 1)} (h0 : 0 < i)
    (hn : i < Fin.last n) : HasLiftingProperty Λ[n, i].ι p :=
  InnerFibration.mem _ (horn_ι_mem_innerHornInclusions h0 hn)

/-!
## Back face in standard successor coordinates

Under `Δ[0] ⋆ Δ[n] ≅ Δ[n + 1]`, the back inclusion is the standard zero face
`d₀`. The under-slice projection therefore reads as face zero of the representing
successor simplex.
-/

/-!
## Standard coordinates for under-slices and left mapping spaces

An `n`-simplex of `X_(x/)` is an `(n + 1)`-simplex of `X` with first vertex `x`.
For the left mapping space `Homᴸ_X(x,y)`, face zero is additionally constant at `y`.
Faces in the slice or mapping space correspond to standard faces with index shifted
by one, and maps induced by `X → Y` act by postcomposition.
-/

/--
The standard zero vertex inclusion `Δ[0] → Δ[n + 1]`.
-/
abbrev vertexZeroStd (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0)

/--
The standard zero vertex inclusion equals the left vertex inclusion transported
through the successor join identification.
-/
lemma vertexZeroStd_eq_leftVertexSucc (n : ℕ) :
    vertexZeroStd n = leftVertexSucc n :=
  (leftVertexSucc_eq n).symm

namespace sliceUnder

variable (X : SSet.{u}) (x : (Δ[0] : SSet.{u}) ⟶ X)

/--
The equivalence between degree-`n` under-slice simplices and maps
`σ : Δ[n + 1] → X` whose zero vertex is the fixed vertex `x`.
-/
def simplexEquivSuccStd (n : ℕ) :
    (sliceUnder X x).obj (op ⦋n⦌) ≃
      { σ : (Δ[n + 1] : SSet.{u}) ⟶ X // vertexZeroStd n ≫ σ = x } :=
  (simplexEquivSucc X x n).trans
    { toFun := fun σ => ⟨SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫ σ.1, by
        calc vertexZeroStd n ≫
              (SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫ σ.1)
            = leftVertex n ≫ σ.1 := by
              rw [vertexZeroStd_eq_leftVertexSucc, leftVertexSucc,
                Category.assoc,
                ← Category.assoc (SSet.stdSimplex.map (zeroAddSuccIso n).hom),
                ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
                CategoryTheory.Functor.map_id, Category.id_comp]
          _ = x := σ.2⟩
      invFun := fun τ => ⟨SSet.stdSimplex.map (zeroAddSuccIso n).hom ≫ τ.1, by
        calc leftVertex n ≫
              (SSet.stdSimplex.map (zeroAddSuccIso n).hom ≫ τ.1)
            = leftVertexSucc n ≫ τ.1 := by
              rw [← Category.assoc]
              rfl
          _ = vertexZeroStd n ≫ τ.1 :=
            congrArg (fun g => g ≫ τ.1)
              (vertexZeroStd_eq_leftVertexSucc n).symm
          _ = x := τ.2⟩
      left_inv := fun σ => by
        apply Subtype.ext
        change SSet.stdSimplex.map (zeroAddSuccIso n).hom ≫
            (SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫ σ.1) = σ.1
        rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
          Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
      right_inv := fun τ => by
        apply Subtype.ext
        change SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫
            (SSet.stdSimplex.map (zeroAddSuccIso n).hom ≫ τ.1) = τ.1
        rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
          Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp] }

/--
The representing standard simplex is obtained from the successor-simplex coordinate
by precomposing with the inverse successor identification.
-/
@[simp]
lemma simplexEquivSuccStd_apply_val (n : ℕ)
    (f : (sliceUnder X x).obj (op ⦋n⦌)) :
    ((simplexEquivSuccStd X x n) f).1 =
      SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫
        ((simplexEquivSucc X x n) f).1 :=
  rfl

/--
The inverse standard-coordinate equivalence recovers the under-slice join map by
precomposition with the forward join and successor identifications.
-/
@[simp]
lemma simplexEquivSuccStd_symm_apply_val (n : ℕ)
    (τ : { σ : (Δ[n + 1] : SSet.{u}) ⟶ X //
      vertexZeroStd n ≫ σ = x }) :
    ((simplexEquivSuccStd X x n).symm τ).1 =
      (joinStdSimplexIso.{u} 0 n).hom ≫
        (SSet.stdSimplex.map (zeroAddSuccIso n).hom ≫ τ.1) :=
  rfl

/--
The map `Δ[n + 1] → X` representing a map `Δ[n] → X_(x/)` under the standard
under-slice coordinate equivalence.
-/
def stdSimplexOf {n : ℕ} (φ : (Δ[n] : SSet.{u}) ⟶ sliceUnder X x) :
    (Δ[n + 1] : SSet.{u}) ⟶ X :=
  ((simplexEquivSuccStd X x n) (yonedaEquiv φ)).1

/--
A map `σ : Δ[n + 1] → X` with zero vertex `x` determines the corresponding
map `Δ[n] → X_(x/)`.
-/
def ofStdSimplex {n : ℕ} (σ : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hσ : vertexZeroStd n ≫ σ = x) :
    (Δ[n] : SSet.{u}) ⟶ sliceUnder X x :=
  yonedaEquiv.symm ((simplexEquivSuccStd X x n).symm ⟨σ, hσ⟩)

/--
Constructing an under-slice map from a standard simplex with zero vertex `x`,
then taking its standard simplex, returns the given simplex.
-/
@[simp]
lemma stdSimplexOf_ofStdSimplex {n : ℕ}
    (σ : (Δ[n + 1] : SSet.{u}) ⟶ X) (hσ : vertexZeroStd n ≫ σ = x) :
    stdSimplexOf X x (ofStdSimplex X x σ hσ) = σ := by
  simp only [stdSimplexOf, ofStdSimplex, Equiv.apply_symm_apply]

/--
The standard simplex representing an under-slice map has zero vertex equal to `x`.
-/
lemma stdSimplexOf_vertex {n : ℕ}
    (φ : (Δ[n] : SSet.{u}) ⟶ sliceUnder X x) :
    vertexZeroStd n ≫ stdSimplexOf X x φ = x :=
  ((simplexEquivSuccStd X x n) (yonedaEquiv φ)).2

/--
Constructing an under-slice map from its representing standard simplex returns
the original under-slice map.
-/
lemma ofStdSimplex_stdSimplexOf {n : ℕ}
    (φ : (Δ[n] : SSet.{u}) ⟶ sliceUnder X x) :
    ofStdSimplex X x (stdSimplexOf X x φ)
      (stdSimplexOf_vertex X x φ) = φ := by
  apply yonedaEquiv.injective
  simp only [ofStdSimplex, Equiv.apply_symm_apply]
  rw [show (⟨stdSimplexOf X x φ, stdSimplexOf_vertex X x φ⟩ :
        { σ : (Δ[n + 1] : SSet.{u}) ⟶ X //
          vertexZeroStd n ≫ σ = x }) =
      (simplexEquivSuccStd X x n) (yonedaEquiv φ) from
    Subtype.ext rfl, Equiv.symm_apply_apply]

/--
Two maps from a standard simplex into the under-slice are equal if their
representing successor simplices in `X` are equal.
-/
theorem ext_of_stdSimplexOf_eq {n : ℕ}
    {φ ψ : (Δ[n] : SSet.{u}) ⟶ sliceUnder X x}
    (h : stdSimplexOf X x φ = stdSimplexOf X x ψ) : φ = ψ := by
  have h1 : (simplexEquivSuccStd X x n) (yonedaEquiv φ) =
      (simplexEquivSuccStd X x n) (yonedaEquiv ψ) :=
    Subtype.ext h
  have h2 : yonedaEquiv φ = yonedaEquiv ψ :=
    (simplexEquivSuccStd X x n).injective h1
  exact yonedaEquiv.injective h2

/--
The projection of an under-slice map to `X` is the zero face of its representing
standard simplex.
-/
theorem proj_eq_δ_zero_comp_stdSimplexOf {n : ℕ}
    (φ : (Δ[n] : SSet.{u}) ⟶ sliceUnder X x) :
    φ ≫ proj X x = stdSimplex.δ (0 : Fin (n + 2)) ≫
      stdSimplexOf X x φ := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  have hkey : (proj X x).app (op ⦋n⦌) (yonedaEquiv φ) =
      yonedaEquiv (stdSimplex.δ (0 : Fin (n + 2)) ≫
        stdSimplexOf X x φ) := by
    rw [proj_apply]
    congr 1
    calc joinInr Δ[0] Δ[n] ≫ (yonedaEquiv φ).1
        = backInclusion n ≫ ((simplexEquivSucc X x n)
            (yonedaEquiv φ)).1 := by
          rw [simplexEquivSucc_apply_val, backInclusion,
            Category.assoc, ← Category.assoc
              (joinStdSimplexIso.{u} 0 n).hom
              (joinStdSimplexIso.{u} 0 n).inv, Iso.hom_inv_id,
            Category.id_comp]
      _ = stdSimplex.δ (0 : Fin (n + 2)) ≫ stdSimplexOf X x φ := by
          rw [stdSimplexOf, simplexEquivSuccStd_apply_val,
            ← backInclusionSucc_eq, backInclusionSucc,
            Category.assoc, ← Category.assoc
              (SSet.stdSimplex.map (zeroAddSuccIso n).hom),
            ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
            CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hkey]

/--
Taking face `a` in the under-slice corresponds to taking standard-simplex face
`a + 1` in `X`.
-/
theorem stdSimplexOf_δ {k : ℕ}
    (φ : (Δ[k + 1] : SSet.{u}) ⟶ sliceUnder X x) (a : Fin (k + 2)) :
    stdSimplexOf X x (stdSimplex.δ a ≫ φ) =
      stdSimplex.δ a.succ ≫ stdSimplexOf X x φ := by
  have hval : ∀ (t : ℕ) (τ : (sliceUnder X x).obj (op ⦋t⦌)),
      ((simplexEquivSuccStd X x t) τ).1 =
        SSet.stdSimplex.map (zeroAddSuccIso t).inv ≫
          ((joinStdSimplexIso.{u} 0 t).inv ≫ τ.1) := fun t τ ↦ rfl
  have hδδ : (sliceUnder X x).δ a (yonedaEquiv φ) =
      yonedaEquiv (stdSimplex.δ a ≫ φ) := by
    have h := stdSimplex.δ_comp_yonedaEquiv_symm
      (X := sliceUnder X x) (x := yonedaEquiv φ) (i := a)
    rw [Equiv.symm_apply_apply] at h
    calc (sliceUnder X x).δ a (yonedaEquiv φ)
        = yonedaEquiv (yonedaEquiv.symm
            ((sliceUnder X x).δ a (yonedaEquiv φ))) :=
          (Equiv.apply_symm_apply _ _).symm
      _ = yonedaEquiv (stdSimplex.δ a ≫ φ) := by rw [← h]
  have hδ : (((sliceUnder X x).δ a (yonedaEquiv φ)) :
        (sliceUnder X x).obj (op ⦋k⦌)).1 =
      (join.{u}.obj (Δ[0] : SSet.{u})).map
          (SSet.stdSimplex.map (SimplexCategory.δ a)) ≫
        (yonedaEquiv φ).1 :=
    sliceUnder.map_val X x _ _
  calc stdSimplexOf X x (stdSimplex.δ a ≫ φ)
      = SSet.stdSimplex.map (zeroAddSuccIso k).inv ≫
          (SSet.stdSimplex.map
            (AugmentedSimplexCategory.tensorHomOf (𝟙 ⦋0⦌)
              (SimplexCategory.δ a)) ≫
            ((joinStdSimplexIso.{u} 0 (k + 1)).inv ≫
              (yonedaEquiv φ).1)) := by
        rw [stdSimplexOf, ← hδδ, hval k, hδ,
          ← Category.assoc (joinStdSimplexIso.{u} 0 k).inv,
          joinStdSimplexIso_inv_comp_join_obj_map, Category.assoc]
    _ = stdSimplex.δ a.succ ≫ stdSimplexOf X x φ := by
        rw [stdSimplexOf, hval (k + 1), ← Category.assoc
            (SSet.stdSimplex.map (zeroAddSuccIso k).inv),
          ← CategoryTheory.Functor.map_comp,
          zeroAddSuccIso_inv_comp_tensorHomOf_id_δ,
          CategoryTheory.Functor.map_comp, ← stdSimplex_δ_eq_map,
          Category.assoc]

/--
Applying the under-slice map induced by `F : X → Y` postcomposes the representing
standard simplex with `F`, changing its fixed vertex from `x` to `F(x)`.
-/
theorem stdSimplexOf_map {Y : SSet.{u}} (F : X ⟶ Y) {n : ℕ}
    (φ : (Δ[n] : SSet.{u}) ⟶ sliceUnder X x) :
    stdSimplexOf Y (x ≫ F) (φ ≫ map X x F) =
      stdSimplexOf X x φ ≫ F := by
  rw [stdSimplexOf, stdSimplexOf, yonedaEquiv_comp]
  change SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫
      ((joinStdSimplexIso.{u} 0 n).inv ≫
        ((map X x F).app (op ⦋n⦌) (yonedaEquiv φ)).1) =
    (SSet.stdSimplex.map (zeroAddSuccIso n).inv ≫
      ((joinStdSimplexIso.{u} 0 n).inv ≫ (yonedaEquiv φ).1)) ≫ F
  rw [map_app_val]
  simp only [Category.assoc]

end sliceUnder

namespace mappingSpaceLeft

variable (X : SSet.{u}) (x y : (Δ[0] : SSet.{u}) ⟶ X)

/--
The successor simplex representing a map into `Homᴸ_X(x,y)`, with zero vertex
`x` and zero face constant at `y`.
-/
def stdSimplexOf {n : ℕ}
    (φ : (Δ[n] : SSet.{u}) ⟶ mappingSpaceLeft X x y) :
    (Δ[n + 1] : SSet.{u}) ⟶ X :=
  sliceUnder.stdSimplexOf X x (φ ≫ toSliceUnder X x y)

/--
The representing standard simplex of a left mapping-space map has zero vertex `x`.
-/
lemma stdSimplexOf_vertex {n : ℕ}
    (φ : (Δ[n] : SSet.{u}) ⟶ mappingSpaceLeft X x y) :
    vertexZeroStd n ≫ stdSimplexOf X x y φ = x :=
  sliceUnder.stdSimplexOf_vertex X x _

/--
The zero face of the representing standard simplex is the constant simplex at
the target vertex `y`.
-/
lemma stdSimplexOf_back {n : ℕ}
    (φ : (Δ[n] : SSet.{u}) ⟶ mappingSpaceLeft X x y) :
    stdSimplex.δ (0 : Fin (n + 2)) ≫ stdSimplexOf X x y φ =
      toDeltaZero (Δ[n] : SSet.{u}) ≫ y := by
  rw [stdSimplexOf, ← sliceUnder.proj_eq_δ_zero_comp_stdSimplexOf,
    Category.assoc, mappingSpaceLeft_toSliceUnder_proj,
    ← Category.assoc, toDeltaZero_eq (φ ≫ toDeltaZero _)]

/--
A successor simplex with zero vertex `x` and zero face constant at `y` determines
a map from the standard simplex into `Homᴸ_X(x,y)`.
-/
def ofStdSimplex {n : ℕ} (σ : (Δ[n + 1] : SSet.{u}) ⟶ X)
    (hv : vertexZeroStd n ≫ σ = x)
    (hb : stdSimplex.δ (0 : Fin (n + 2)) ≫ σ =
      toDeltaZero (Δ[n] : SSet.{u}) ≫ y) :
    (Δ[n] : SSet.{u}) ⟶ mappingSpaceLeft X x y :=
  yonedaEquiv.symm
    ⟨(yonedaEquiv (sliceUnder.ofStdSimplex X x σ hv)).1,
      (yonedaEquiv (sliceUnder.ofStdSimplex X x σ hv)).2, by
      have hsimplex : yonedaEquiv
            (sliceUnder.ofStdSimplex X x σ hv) =
          (sliceUnder.simplexEquivSuccStd X x n).symm ⟨σ, hv⟩ := by
        simp only [sliceUnder.ofStdSimplex, Equiv.apply_symm_apply]
      calc joinInr Δ[0] (stdSimplex.obj (op ⦋n⦌).unop) ≫
            (yonedaEquiv (sliceUnder.ofStdSimplex X x σ hv)).1
          = backInclusion n ≫
              (SSet.stdSimplex.map (zeroAddSuccIso n).hom ≫ σ) := by
            rw [hsimplex, sliceUnder.simplexEquivSuccStd_symm_apply_val,
              backInclusion, Category.assoc]
        _ = backInclusionSucc n ≫ σ := by
            rw [backInclusionSucc, Category.assoc]
        _ = toDeltaZero (stdSimplex.obj (op ⦋n⦌).unop) ≫ y := by
            rw [backInclusionSucc_eq]
            exact hb⟩

/--
The left mapping-space map constructed from a standard simplex, followed by its
under-slice inclusion, is the under-slice map constructed from that same simplex.
-/
lemma ofStdSimplex_comp_toSliceUnder {n : ℕ}
    (σ : (Δ[n + 1] : SSet.{u}) ⟶ X) (hv : vertexZeroStd n ≫ σ = x)
    (hb : stdSimplex.δ (0 : Fin (n + 2)) ≫ σ =
      toDeltaZero (Δ[n] : SSet.{u}) ≫ y) :
    ofStdSimplex X x y σ hv hb ≫ toSliceUnder X x y =
      sliceUnder.ofStdSimplex X x σ hv := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  apply Subtype.ext
  calc ((toSliceUnder X x y).app (op ⦋n⦌)
        (yonedaEquiv (ofStdSimplex X x y σ hv hb))).1
      = (yonedaEquiv (ofStdSimplex X x y σ hv hb)).1 :=
        toSliceUnder_app_val X x y _
    _ = (yonedaEquiv (sliceUnder.ofStdSimplex X x σ hv)).1 :=
        congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/--
Constructing a left mapping-space map from a standard simplex satisfying the
two endpoint conditions, then reading its standard simplex, returns that simplex.
-/
@[simp]
lemma stdSimplexOf_ofStdSimplex {n : ℕ}
    (σ : (Δ[n + 1] : SSet.{u}) ⟶ X) (hv : vertexZeroStd n ≫ σ = x)
    (hb : stdSimplex.δ (0 : Fin (n + 2)) ≫ σ =
      toDeltaZero (Δ[n] : SSet.{u}) ≫ y) :
    stdSimplexOf X x y (ofStdSimplex X x y σ hv hb) = σ := by
  rw [stdSimplexOf, ofStdSimplex_comp_toSliceUnder,
    sliceUnder.stdSimplexOf_ofStdSimplex]

/--
Two maps into a left mapping space are equal if their representing standard
successor simplices are equal.
-/
theorem ext_of_stdSimplexOf_eq {n : ℕ}
    {φ ψ : (Δ[n] : SSet.{u}) ⟶ mappingSpaceLeft X x y}
    (h : stdSimplexOf X x y φ = stdSimplexOf X x y ψ) : φ = ψ := by
  have h' : sliceUnder.stdSimplexOf X x (φ ≫ toSliceUnder X x y) =
      sliceUnder.stdSimplexOf X x (ψ ≫ toSliceUnder X x y) := h
  have h2 : φ ≫ toSliceUnder X x y = ψ ≫ toSliceUnder X x y :=
    sliceUnder.ext_of_stdSimplexOf_eq X x h'
  apply yonedaEquiv.injective
  apply Subtype.ext
  calc (yonedaEquiv φ).1
      = ((toSliceUnder X x y).app (op ⦋n⦌) (yonedaEquiv φ)).1 :=
        (toSliceUnder_app_val X x y _).symm
    _ = (yonedaEquiv ψ).1 := by
        rw [← yonedaEquiv_comp, h2, yonedaEquiv_comp,
          toSliceUnder_app_val]

/--
Constructing a left mapping-space map from its representing standard simplex
returns the original map.
-/
lemma ofStdSimplex_stdSimplexOf {n : ℕ}
    (φ : (Δ[n] : SSet.{u}) ⟶ mappingSpaceLeft X x y) :
    ofStdSimplex X x y (stdSimplexOf X x y φ)
        (stdSimplexOf_vertex X x y φ) (stdSimplexOf_back X x y φ) =
      φ :=
  ext_of_stdSimplexOf_eq X x y (stdSimplexOf_ofStdSimplex X x y _ _ _)

/--
Taking face `a` of a left mapping-space map corresponds to taking face `a + 1`
of its standard successor simplex.
-/
theorem stdSimplexOf_δ {k : ℕ}
    (φ : (Δ[k + 1] : SSet.{u}) ⟶ mappingSpaceLeft X x y)
    (a : Fin (k + 2)) :
    stdSimplexOf X x y (stdSimplex.δ a ≫ φ) =
      stdSimplex.δ a.succ ≫ stdSimplexOf X x y φ := by
  rw [stdSimplexOf, stdSimplexOf, Category.assoc,
    sliceUnder.stdSimplexOf_δ]

/--
The map on left mapping spaces induced by `F : X → Y` postcomposes each
representing standard simplex with `F`, sending its endpoint vertices to `F(x),F(y)`.
-/
theorem stdSimplexOf_map {Y : SSet.{u}} (F : X ⟶ Y) {n : ℕ}
    (φ : (Δ[n] : SSet.{u}) ⟶ mappingSpaceLeft X x y) :
    stdSimplexOf Y (x ≫ F) (y ≫ F) (φ ≫ map X x y F) =
      stdSimplexOf X x y φ ≫ F := by
  rw [stdSimplexOf, stdSimplexOf, Category.assoc, map_toSliceUnder,
    ← Category.assoc, sliceUnder.stdSimplexOf_map]

end mappingSpaceLeft

/-!
## Under-slice comparison and inner horn lifting

A left horn in the under-slice comparison has nonfinal missing index `i`.
Its lifted face family in `X` has missing index `i + 1`, an inner index; face zero
comes from the underlying component of the bottom pullback simplex. Inner-fibration
lifting of `p` therefore supplies a left-horn lift in the comparison.
-/

/-- The `0`-th vertex is preserved by face maps omitting a
positive vertex, at the level of standard vertex inclusions. -/
private lemma vertexZeroStd_comp_δ_succ {n : ℕ} (a : Fin (n + 2)) :
    vertexZeroStd n ≫ stdSimplex.δ a.succ = vertexZeroStd (n + 1) := by
  have h1 : (SimplexCategory.δ a.succ).toOrderHom 0 = 0 := by
    change Fin.succAbove a.succ (0 : Fin (n + 2)) = (0 : Fin (n + 3))
    simp [Fin.succAbove]
  rw [stdSimplex_δ_eq_map, ← CategoryTheory.Functor.map_comp,
    SimplexCategory.const_comp, h1]

/--
For any inner fibration `p : X → S` and vertex `x` of `X`, the comparison
`X_(x/) → S_(px/) ×_S X` is a left fibration.
-/
theorem leftFibration_sliceUnderComparison {p : X ⟶ S}
    [InnerFibration p] (x : (Δ[0] : SSet.{u}) ⟶ X) :
    LeftFibration (sliceUnderComparison (p := p) x) := by
  apply leftFibration_of_hasLiftingProperty_horn
  intro m i hi
  obtain _ | n := m
  · exfalso
    exact Nat.not_lt_zero i.val hi
  · refine ⟨?_⟩
    intro top bottom sq
    -- The bottom map, its two components, and its standard simplex.
    set v₁ : (Δ[n + 1] : SSet.{u}) ⟶ sliceUnder S (x ≫ p) :=
      bottom ≫ pullback.fst (sliceUnder.proj S (x ≫ p)) p with hv₁
    set v₂ : (Δ[n + 1] : SSet.{u}) ⟶ X :=
      bottom ≫ pullback.snd (sliceUnder.proj S (x ≫ p)) p with hv₂
    set T : (Δ[n + 2] : SSet.{u}) ⟶ S :=
      sliceUnder.stdSimplexOf S (x ≫ p) v₁ with hT
    -- The transposed horn family in `X`.
    set g : ∀ (k : Fin (n + 3)) (_ : k ≠ i.succ),
        (Δ[n + 1] : SSet.{u}) ⟶ X := fun k hk =>
      if h0 : k = 0 then v₂
      else sliceUnder.stdSimplexOf X x
        (horn.ι i (k.pred h0) (fun h => hk (by
          rw [← Fin.succ_pred k h0, h])) ≫ top) with hg
    have htopw : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
        horn.ι i j hj ≫ (top ≫ sliceUnderComparison (p := p) x) =
          stdSimplex.δ j ≫ bottom := by
      intro j hj
      rw [sq.w, ← Category.assoc, horn.ι_ι]
    have htop_proj : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
        (horn.ι i j hj ≫ top) ≫ sliceUnder.proj X x =
          stdSimplex.δ j ≫ v₂ := by
      intro j hj
      calc (horn.ι i j hj ≫ top) ≫ sliceUnder.proj X x
          = (horn.ι i j hj ≫ (top ≫
              sliceUnderComparison (p := p) x)) ≫
              pullback.snd (sliceUnder.proj S (x ≫ p)) p := by
            rw [← sliceUnderComparison_snd (p := p) x]
            simp only [Category.assoc]
        _ = stdSimplex.δ j ≫ v₂ := by
            rw [htopw j hj, Category.assoc]
    have htop_map : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
        (horn.ι i j hj ≫ top) ≫ sliceUnder.map X x p =
          stdSimplex.δ j ≫ v₁ := by
      intro j hj
      calc (horn.ι i j hj ≫ top) ≫ sliceUnder.map X x p
          = (horn.ι i j hj ≫ (top ≫
              sliceUnderComparison (p := p) x)) ≫
              pullback.fst (sliceUnder.proj S (x ≫ p)) p := by
            rw [← sliceUnderComparison_fst (p := p) x]
            simp only [Category.assoc]
        _ = stdSimplex.δ j ≫ v₁ := by
            rw [htopw j hj, Category.assoc]
    have hg_zero : ∀ (h : (0 : Fin (n + 3)) ≠ i.succ), g 0 h = v₂ :=
      fun h => dite_eq_left rfl
    have hg_succ : ∀ (j : Fin (n + 2)) (hj : j ≠ i)
        (h : j.succ ≠ i.succ), g j.succ h =
        sliceUnder.stdSimplexOf X x (horn.ι i j hj ≫ top) := by
      intro j hj h
      rw [hg]
      simp only [dite_eq_right (Fin.succ_ne_zero j), Fin.pred_succ]
    have hf : horn.IsCompatible
        (fun j hj => horn.ι i j hj ≫ top) :=
      horn.IsCompatible.of_hom top
    have hgcompat : horn.IsCompatible g := by
      rw [horn.isCompatible_iff]
      intro j k hj hk hjk
      by_cases hj0 : j = 0
      · subst hj0
        obtain ⟨c, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
        have hc : c ≠ i := fun h => hk (by rw [h])
        have e1 : (c.succ).pred (Fin.ne_zero_of_lt hjk) = c :=
          Fin.pred_succ c
        have e2 : (0 : Fin (n + 3)).castPred (Fin.ne_last_of_lt hjk) =
            0 := Fin.ext (Fin.coe_castPred _ _)
        rw [e1, e2, hg_zero, hg_succ c hc,
          ← sliceUnder.proj_eq_δ_zero_comp_stdSimplexOf,
          htop_proj c hc]
      · by_cases hn0 : n = 0
        · subst hn0
          exfalso
          have hjv : j.val ≠ i.val + 1 :=
            fun h => hj (Fin.ext h)
          have hkv : k.val ≠ i.val + 1 :=
            fun h => hk (Fin.ext h)
          have hj0v : j.val ≠ 0 := fun h => hj0 (Fin.ext h)
          have hlt : j.val < k.val := hjk
          have hb1 := j.is_lt
          have hb2 := k.is_lt
          have hb3 := i.is_lt
          omega
        · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
          obtain ⟨a, rfl⟩ := j.eq_succ_of_ne_zero hj0
          obtain ⟨c, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
          have ha : a ≠ i := fun h => hj (by rw [h])
          have hc : c ≠ i := fun h => hk (by rw [h])
          have hac : a < c := by
            have h2 : a.succ.val < c.succ.val := hjk
            simp only [Fin.val_succ, Nat.add_lt_add_iff_right] at h2
            exact h2
          have hc0 : c ≠ 0 := by
            intro h
            rw [h] at hac
            exact Nat.not_lt_zero a.val hac
          have e1 : (c.succ).pred (Fin.ne_zero_of_lt hjk) =
              (c.pred hc0).succ := by
            rw [Fin.pred_succ, Fin.succ_pred]
          have e2 : (a.succ).castPred (Fin.ne_last_of_lt hjk) =
              (a.castPred (Fin.ne_last_of_lt hac)).succ :=
            Fin.ext (by simp [Fin.coe_castPred])
          rw [e1, e2, hg_succ a ha, hg_succ c hc,
            ← sliceUnder.stdSimplexOf_δ X x (horn.ι i a ha ≫ top)
              (c.pred hc0),
            ← sliceUnder.stdSimplexOf_δ X x (horn.ι i c hc ≫ top)
              (a.castPred (Fin.ne_last_of_lt hac)),
            hf.δ_pred_comp a c ha hc hac]
    have hgcomm : ∀ (k : Fin (n + 3)) (hk : k ≠ i.succ),
        g k hk ≫ p = stdSimplex.δ k ≫ T := by
      intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        rw [hg_zero]
        calc v₂ ≫ p = v₁ ≫ sliceUnder.proj S (x ≫ p) := by
              rw [hv₁, hv₂, Category.assoc, Category.assoc,
                pullback.condition]
          _ = stdSimplex.δ (0 : Fin (n + 3)) ≫ T :=
            sliceUnder.proj_eq_δ_zero_comp_stdSimplexOf S (x ≫ p) v₁
      · obtain ⟨c, rfl⟩ := k.eq_succ_of_ne_zero hk0
        have hc : c ≠ i := fun h => hk (by rw [h])
        rw [hg_succ c hc, ← sliceUnder.stdSimplexOf_map X x p,
          htop_map c hc, sliceUnder.stdSimplexOf_δ]
    have h0succ : (0 : Fin (n + 3)) < i.succ := by
      simp only [Fin.lt_def, Fin.val_zero, Fin.val_succ]
      omega
    have hnsucc : i.succ < Fin.last (n + 2) := by
      have h2 : i.val < (Fin.last (n + 1)).val := hi
      simp only [Fin.val_last] at h2
      simp only [Fin.lt_def, Fin.val_succ, Fin.val_last]
      omega
    obtain ⟨Phi, hPhiFaces, hPhiP⟩ := exists_simplex_lift_horn hgcompat
      (innerFibration_hasLiftingProperty_horn h0succ hnsucc) T hgcomm
    -- The filler lies in the under-slice.
    obtain ⟨j₀, hj₀⟩ : ∃ j : Fin (n + 2), j ≠ i := by
      by_cases hi0 : i = 0
      · exact ⟨1, by simp [hi0]⟩
      · exact ⟨0, Ne.symm hi0⟩
    have hj₀succ : j₀.succ ≠ i.succ := by
      simp only [ne_eq, Fin.succ_inj]
      exact hj₀
    have hvertex : vertexZeroStd (n + 1) ≫ Phi = x := by
      calc vertexZeroStd (n + 1) ≫ Phi
          = vertexZeroStd n ≫ (stdSimplex.δ j₀.succ ≫ Phi) := by
            rw [← Category.assoc, vertexZeroStd_comp_δ_succ]
        _ = x := by
            rw [hPhiFaces j₀.succ hj₀succ, hg_succ j₀ hj₀,
              sliceUnder.stdSimplexOf_vertex]
    refine ⟨⟨CommSq.LiftStruct.mk
      (sliceUnder.ofStdSimplex X x Phi hvertex) ?_ ?_⟩⟩
    · apply horn.hom_ext'
      intro j hj
      rw [← Category.assoc, horn.ι_ι]
      apply sliceUnder.ext_of_stdSimplexOf_eq X x
      rw [sliceUnder.stdSimplexOf_δ,
        sliceUnder.stdSimplexOf_ofStdSimplex,
        hPhiFaces j.succ (by simp only [ne_eq, Fin.succ_inj]; exact hj),
        hg_succ j hj]
    · apply pullback.hom_ext
      · calc (sliceUnder.ofStdSimplex X x Phi hvertex ≫
              sliceUnderComparison (p := p) x) ≫
              pullback.fst (sliceUnder.proj S (x ≫ p)) p
            = sliceUnder.ofStdSimplex X x Phi hvertex ≫
                sliceUnder.map X x p := by
              rw [Category.assoc, sliceUnderComparison_fst]
          _ = bottom ≫
              pullback.fst (sliceUnder.proj S (x ≫ p)) p := by
              apply sliceUnder.ext_of_stdSimplexOf_eq S (x ≫ p)
              rw [sliceUnder.stdSimplexOf_map,
                sliceUnder.stdSimplexOf_ofStdSimplex, hPhiP]
      · calc (sliceUnder.ofStdSimplex X x Phi hvertex ≫
              sliceUnderComparison (p := p) x) ≫
              pullback.snd (sliceUnder.proj S (x ≫ p)) p
            = sliceUnder.ofStdSimplex X x Phi hvertex ≫
                sliceUnder.proj X x := by
              rw [Category.assoc, sliceUnderComparison_snd]
          _ = bottom ≫
              pullback.snd (sliceUnder.proj S (x ≫ p)) p := by
              rw [sliceUnder.proj_eq_δ_zero_comp_stdSimplexOf,
                sliceUnder.stdSimplexOf_ofStdSimplex,
                hPhiFaces 0 (Fin.succ_ne_zero i).symm, hg_zero]

/-- Instance form of `SSet.leftFibration_sliceUnderComparison`. -/
instance {p : X ⟶ S} [InnerFibration p]
    (x : (Δ[0] : SSet.{u}) ⟶ X) :
    LeftFibration (sliceUnderComparison (p := p) x) :=
  leftFibration_sliceUnderComparison x

end SSet

end
