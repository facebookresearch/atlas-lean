/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeSimplexDeformation
public import MathlibExt.AlgebraicTopology.SimplicialCategory.WalkingAdjunction.FatConeVertices
public import MathlibExt.AlgebraicTopology.Quasicategory.PointwiseEquivalence
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.HoPreNatIso

/-!
# The actual standard-simplex fat-cone comparison is categorical

The proved whole deformation fixes every original base and apex
vertex. Evaluation in every quasicategory therefore makes the entire
deformation edge invertible, by the existing pointwise theorem. Its
actual precomposition natural transformation and the strict section
identity prove the defining hFun equivalence for the original
fat-cone comparison on each standard simplex. No quasicategory
assumption on the fat cone itself or natural simplex section is used.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open scoped Simplicial

namespace SSet.WalkingAdjunction.FatCone

/-- The complete path of every original fat-cone vertex is its identical constant path. -/
theorem vertex_wholePath (n : ℕ) (x : (obj (Δ[n] : SSet.{u})) _⦋0⦌) :
    SSet.yonedaEquiv.symm x ≫ wholePath n =
      SSet.yonedaEquiv.symm x ≫ constPath (obj Δ[n]) := by
  obtain ⟨a, rfl⟩ | ⟨z, rfl⟩ := vertex_base_or_apex (Δ[n] : SSet.{u}) x
  · rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, base_wholePath, ← Category.assoc]
  · rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, apex_wholePath, ← Category.assoc]

/-- Restricting the entire actual deformation to any original vertex gives its full constant cylinder. -/
theorem wholeDeformation_point (n : ℕ) (x : (obj (Δ[n] : SSet.{u})) _⦋0⦌) :
    (SSet.yonedaEquiv.symm x ▷ (Δ[1] : SSet.{u})) ≫ (wholeDeformation n).h =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) Δ[1] ≫ SSet.yonedaEquiv.symm x := by
  have he := congrArg MonoidalClosed.uncurry (vertex_wholePath n x)
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_left,
    uncurry_constPath, CartesianMonoidalCategory.whiskerLeft_snd] at he
  rw [wholeDeformation, Homotopy.mkOfH_h, BraidedCategory.braiding_naturality_left_assoc, he]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun p => p ≫ SSet.yonedaEquiv.symm x)
      (CartesianMonoidalCategory.braiding_hom_snd _ _))

private theorem homotopy_pre_vertex_equivalence {X C : SSet.{u}} {f g : X ⟶ C}
    (H : Homotopy f g) (v : (Δ[0] : SSet.{u}) ⟶ X)
    (hv : (v ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.fst (Δ[0] : SSet.{u}) Δ[1] ≫ v ≫ f) :
    (H.edgeIhom.map ((pre v).app C)).IsEquivalence := by
  have he : (H.edgeIhom.map ((pre v).app C)).edge =
      (Edge.id (ihomVertexEquiv Δ[0] C (v ≫ f))).edge := by
    rw [Edge.map_edge_yoneda, Homotopy.edgeIhom_edge, Equiv.symm_apply_apply,
      MonoidalClosed.curry_pre_app, hv]
    have hi := congrArg Edge.edge (Homotopy.edgeIhom_reflH (v ≫ f))
    simpa only [Homotopy.edgeIhom_edge, Homotopy.reflH_h, Category.assoc] using hi
  exact (Edge.isEquivalence_iff_of_edge_eq he).mpr (Edge.isEquivalence_id _)

/-- Every actual whole deformation edge in a quasicategory probe is an equivalence. -/
theorem wholeDeformation_postcomp_equivalence (n : ℕ) (C : SSet.{u}) [Quasicategory C]
    (q : obj (Δ[n] : SSet.{u}) ⟶ C) : ((wholeDeformation n).postcomp q).edgeIhom.IsEquivalence := by
  apply (Edge.isEquivalence_iff_forall_eval_vertex _).mpr
  intro x
  apply Edge.IsEquivalence.map
  apply homotopy_pre_vertex_equivalence
  rw [Homotopy.postcomp_h, ← Category.assoc, wholeDeformation_point, Category.assoc, Category.id_comp]

/-- The actual precomposition transformation of the whole deformation is a natural isomorphism in every probe. -/
def deformationPreIso (n : ℕ) (C : SSet.{u}) [Quasicategory C] :
    (hoFunctor.map ((pre (𝟙 (obj (Δ[n] : SSet.{u})))).app C)).toFunctor ≅
      (hoFunctor.map ((pre (retraction n)).app C)).toFunctor := by
  let t := (wholeDeformation n).hoPreNatTrans C
  let _ : ∀ x, IsIso (t.app x) := by
    intro x
    let v := HomotopyCategory.objEquiv x
    have hx : HomotopyCategory.mk v = x := HomotopyCategory.objEquiv.left_inv x
    rw [← hx]
    change IsIso (((wholeDeformation n).hoPreNatTrans C).app (HomotopyCategory.mk v))
    rw [Homotopy.hoPreNatTrans_app_mk]
    have he : ((wholeDeformation n).hoPreCompEdge C v).IsEquivalence :=
      (Edge.isEquivalence_iff_of_edge_eq (Homotopy.hoPreCompEdge_edge _ _ _)).mpr
        (wholeDeformation_postcomp_equivalence n C ((ihomVertexEquiv _ C).symm v))
    exact he
  let _ : IsIso t := NatIso.isIso_of_isIso_app t
  exact asIso t

/-- The actual standard-simplex fat-cone comparison satisfies the original defining categorical-equivalence test. -/
theorem toJoin_stdSimplex_categoricalEquivalence (n : ℕ) :
    categoricalEquivalences (toJoin (Δ[n] : SSet.{u})) := by
  intro C hC
  let _ := hC
  let F := (hoFunctor.map ((pre (toJoin (Δ[n] : SSet.{u}))).app C)).toFunctor
  let G := (hoFunctor.map ((pre (joinSection.{u} n)).app C)).toFunctor
  have hFG : F ⋙ G = 𝟭 (hoFunctor.obj ((ihom (Δ[n] ⋆ (Δ[0] : SSet.{u}))).obj C)) := by
    change (hoFunctor.map ((pre (toJoin (Δ[n] : SSet.{u}))).app C)).toFunctor ⋙
      (hoFunctor.map ((pre (joinSection n)).app C)).toFunctor = _
    rw [← hoFunctor_pre_comp, joinSection_toJoin, hoFunctor_pre_id]
  have hGF : (hoFunctor.map ((pre (retraction.{u} n)).app C)).toFunctor = G ⋙ F :=
    hoFunctor_pre_comp C _ _
  let e : 𝟭 (hoFunctor.obj ((ihom (obj (Δ[n] : SSet.{u}))).obj C)) ≅ G ⋙ F :=
    (eqToIso (hoFunctor_pre_id C)).symm ≪≫ deformationPreIso n C ≪≫ eqToIso hGF
  exact Functor.IsEquivalence.mk' G (eqToIso hFG).symm e.symm

end SSet.WalkingAdjunction.FatCone
