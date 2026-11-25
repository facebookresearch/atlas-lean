/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.NondegenerateNerveFunctor
public import MathlibExt.AlgebraicTopology.SimplicialSet.Subdivision.Iterate
public import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit

/-!
# Nonsingular categorical subdivision

Subdivision maps naturally to the nerve of the ordered type of nondegenerate
simplices.  For a nonsingular simplicial set this comparison is an
isomorphism; consequently subdivision and all its iterates are nonsingular.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet

private noncomputable def stdSimplexIsoNerve :
    SSet.stdSimplex.{u} ≅
      SimplexCategory.toPartOrd ⋙ PartOrd.nerveFunctor :=
  NatIso.ofComponents
    (fun n => SSet.stdSimplex.isoNerve.{u} n.len)
    (fun f => by
      ext d s
      apply ComposableArrows.ext
        (h := fun i => by
          change ULift.up (f.toOrderHom
            ((SSet.stdSimplex.objEquiv s).toOrderHom i)) =
            ULift.up (f.toOrderHom
              ((SSet.stdSimplex.objEquiv s).toOrderHom i))
          rfl)
        (w := by
          intro i hi
          subsingleton))

private noncomputable def representableIso :
    SSet.stdSimplex.{u} ⋙ nondegenerateNerve ≅
      SimplexCategory.sd := by
  let e0 := (Functor.associator SSet.stdSimplex.{u}
    SSet.N.functor PartOrd.nerveFunctor).symm
  let e1 := Functor.isoWhiskerRight
    (Functor.isoWhiskerRight stdSimplexIsoNerve SSet.N.functor)
    PartOrd.nerveFunctor
  let e2 := Functor.associator
    (SimplexCategory.toPartOrd ⋙ PartOrd.nerveFunctor)
    SSet.N.functor PartOrd.nerveFunctor
  let e3 := Functor.associator SimplexCategory.toPartOrd
    PartOrd.nerveFunctor (SSet.N.functor ⋙ PartOrd.nerveFunctor)
  let e4 := Functor.isoWhiskerLeft SimplexCategory.toPartOrd
    (Functor.isoWhiskerRight PartOrd.nerveFunctorCompNFunctorIso
      PartOrd.nerveFunctor)
  let e5 := (Functor.associator SimplexCategory.toPartOrd
    PartOrd.nonemptyFiniteChainsFunctor PartOrd.nerveFunctor).symm
  exact e0 ≪≫ e1 ≪≫ e2 ≪≫ e3 ≪≫ e4 ≪≫ e5

/-- The natural comparison from subdivision to the nerve of nondegenerate
simplices. -/
@[no_expose]
noncomputable def sdToNondegenerateNerve :
    SSet.sd.{u} ⟶ SSet.nondegenerateNerve.{u} :=
  SSet.sd.descOfIsLeftKanExtension SSet.stdSimplex.sdIso.inv
    SSet.nondegenerateNerve representableIso.inv

private theorem sdToNondegenerateNerve_stdSimplex_app_isIso
    (n : SimplexCategory) :
    IsIso (sdToNondegenerateNerve.app (SSet.stdSimplex.obj n)) := by
  have h := SSet.sd.descOfIsLeftKanExtension_fac_app
    SSet.stdSimplex.sdIso.inv SSet.nondegenerateNerve
    representableIso.inv n
  change IsIso ((SSet.sd.descOfIsLeftKanExtension
    SSet.stdSimplex.sdIso.inv SSet.nondegenerateNerve
    representableIso.inv).app (SSet.stdSimplex.obj n))
  exact IsIso.of_isIso_fac_left h

private theorem N_map_le_iff_of_mono {X Y : SSet.{u}}
    (f : X ⟶ Y) [Mono f] (x y : X.N) :
    SSet.N.map f x ≤ SSet.N.map f y ↔ x ≤ y := by
  rw [SSet.N.le_iff, SSet.N.le_iff,
    SSet.N.map_subcomplex, SSet.N.map_subcomplex,
    SSet.Subcomplex.image_le_image_iff]

private theorem N_map_injective_of_mono {X Y : SSet.{u}}
    (f : X ⟶ Y) [Mono f] :
    Function.Injective (SSet.N.map f) := by
  intro x y h
  apply le_antisymm
  · exact (N_map_le_iff_of_mono f x y).mp h.le
  · exact (N_map_le_iff_of_mono f y x).mp h.ge

private def topCarrier {X : SSet.{u}} (a : X.N) :
    (Δ[a.dim] : SSet.{u}).N :=
  SSet.N.mk (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋a.dim⦌))
    (SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate a.dim)

private theorem le_topCarrier {X : SSet.{u}} (a : X.N)
    (z : (Δ[a.dim] : SSet.{u}).N) :
    z ≤ topCarrier a := by
  rw [SSet.N.le_iff]
  change SSet.Subcomplex.ofSimplex z.simplex ≤
    SSet.Subcomplex.ofSimplex
      (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋a.dim⦌))
  rw [SSet.stdSimplex.ofSimplex_objEquiv_symm_id]
  exact le_top

private theorem map_topCarrier {X : SSet.{u}} (a : X.N) :
    SSet.N.map (SSet.yonedaEquiv.symm a.simplex) (topCarrier a) = a := by
  let y := SSet.yonedaEquiv.symm a.simplex
  have hnon : y.app _ (topCarrier a).simplex ∈
      X.nonDegenerate (topCarrier a).dim := by
    change X.map (𝟙 ⦋a.dim⦌).op a.simplex ∈ X.nonDegenerate a.dim
    simpa using a.nonDegenerate
  rw [SSet.N.map_eq_mk _ _ hnon, SSet.N.ext_iff]
  change SSet.S.mk
      (y.app _ (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋a.dim⦌))) = a.toS
  rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
  simp

private theorem imageLE {X : SSet.{u}} (a : X.N)
    (z : (Δ[a.dim] : SSet.{u}).N) :
    SSet.N.map (SSet.yonedaEquiv.symm a.simplex) z ≤ a :=
  calc
    SSet.N.map (SSet.yonedaEquiv.symm a.simplex) z ≤
        SSet.N.map (SSet.yonedaEquiv.symm a.simplex) (topCarrier a) :=
      (SSet.N.map (SSet.yonedaEquiv.symm a.simplex)).monotone
        (le_topCarrier a z)
    _ = a := map_topCarrier a

private noncomputable def faceOfLE {X : SSet.{u}} [X.Nonsingular]
    {x a : X.N} (h : x ≤ a) :
    (Δ[a.dim] : SSet.{u}).N := by
  let f := SSet.N.monoOfLE h
  have hf : Mono f := by
    dsimp [f]
    infer_instance
  have hf' : Mono
      (SSet.stdSimplex.objEquiv.{u}
        (SSet.stdSimplex.objEquiv.{u}.symm f)) := by
    change Mono f
    exact hf
  exact SSet.N.mk (SSet.stdSimplex.objEquiv.symm f)
    ((SSet.stdSimplex.mem_nonDegenerate_iff_mono _).2 hf')

private theorem map_faceOfLE {X : SSet.{u}} [X.Nonsingular]
    {x a : X.N} (h : x ≤ a) :
    SSet.N.map (SSet.yonedaEquiv.symm a.simplex) (faceOfLE h) = x := by
  let f := SSet.N.monoOfLE h
  have himage :
      (SSet.yonedaEquiv.symm a.simplex).app _
          (SSet.stdSimplex.objEquiv.symm f) = x.simplex := by
    rw [SSet.yonedaEquiv_symm_app_objEquiv_symm]
    exact SSet.N.map_monoOfLE h
  have hnon :
      (SSet.yonedaEquiv.symm a.simplex).app _
          (faceOfLE h).simplex ∈ X.nonDegenerate (faceOfLE h).dim := by
    change (SSet.yonedaEquiv.symm a.simplex).app _
        (SSet.stdSimplex.objEquiv.symm f) ∈ X.nonDegenerate x.dim
    rw [himage]
    exact x.nonDegenerate
  rw [SSet.N.map_eq_mk _ _ hnon, SSet.N.ext_iff]
  change SSet.S.mk
      ((SSet.yonedaEquiv.symm a.simplex).app _
        (SSet.stdSimplex.objEquiv.symm f)) = x.toS
  rw [himage]

set_option linter.style.haveILetI false in
private noncomputable def liftChain {X : SSet.{u}} [X.Nonsingular]
    {d : ℕ} (c : (CategoryTheory.nerve X.N) _⦋d⦌) :
    (SSet.nondegenerateNerve.obj
      (Δ[(c.obj (Fin.last d)).dim] : SSet.{u})) _⦋d⦌ :=
  (show Fin (d + 1) →o
      (Δ[(c.obj (Fin.last d)).dim] : SSet.{u}).N from
    { toFun := fun j => faceOfLE (c.monotone (Fin.le_last j))
      monotone' := fun i j hij => by
        let y := SSet.yonedaEquiv.symm (c.obj (Fin.last d)).simplex
        haveI : Mono y := SSet.Nonsingular.mono'
          (c.obj (Fin.last d)).simplex
          (c.obj (Fin.last d)).nonDegenerate
        rw [← N_map_le_iff_of_mono y, map_faceOfLE, map_faceOfLE]
        exact c.monotone hij }).monotone.functor

private theorem map_liftChain {X : SSet.{u}} [X.Nonsingular]
    {d : ℕ} (c : (CategoryTheory.nerve X.N) _⦋d⦌) :
    (SSet.nondegenerateNerve.map
      (SSet.yonedaEquiv.symm (c.obj (Fin.last d)).simplex)).app _
        (liftChain c) = c := by
  apply ComposableArrows.ext
    (h := fun j => by
      change SSet.N.map
        (SSet.yonedaEquiv.symm (c.obj (Fin.last d)).simplex)
        (faceOfLE (c.monotone (Fin.le_last j))) = c.obj j
      exact map_faceOfLE _)
    (w := by
      intro i hi
      subsingleton)

private noncomputable def imageChain {X : SSet.{u}} [X.Nonsingular]
    {d : ℕ} (a : X.N)
    (s : (SSet.nondegenerateNerve.obj
      (Δ[a.dim] : SSet.{u})) _⦋d⦌) :
    (SSet.nondegenerateNerve.obj X) _⦋d⦌ :=
  (SSet.nondegenerateNerve.map
    (SSet.yonedaEquiv.symm a.simplex)).app _ s

private theorem lastImageLE {X : SSet.{u}} [X.Nonsingular]
    {d : ℕ} (a : X.N)
    (s : (SSet.nondegenerateNerve.obj
      (Δ[a.dim] : SSet.{u})) _⦋d⦌) :
    (imageChain a s).obj (Fin.last d) ≤ a := by
  change SSet.N.map (SSet.yonedaEquiv.symm a.simplex)
      (s.obj (Fin.last d)) ≤ a
  exact imageLE a (s.obj (Fin.last d))

set_option linter.style.haveILetI false in
private theorem map_liftChain_to_stage
    {X : SSet.{u}} [X.Nonsingular] {d : ℕ} (a : X.N)
    (s : (SSet.nondegenerateNerve.obj
      (Δ[a.dim] : SSet.{u})) _⦋d⦌) :
    (SSet.nondegenerateNerve.map
      (SSet.stdSimplex.map (SSet.N.monoOfLE (lastImageLE a s)))).app _
        (liftChain (imageChain a s)) = s := by
  let y := SSet.yonedaEquiv.symm a.simplex
  haveI : Mono y := SSet.Nonsingular.mono' a.simplex a.nonDegenerate
  apply ComposableArrows.ext
    (h := fun j => by
      apply N_map_injective_of_mono y
      change SSet.N.map y
          (SSet.N.map
            (SSet.stdSimplex.map (SSet.N.monoOfLE (lastImageLE a s)))
            (faceOfLE _)) =
        SSet.N.map y (s.obj j)
      rw [SSet.N.map_comp_apply]
      have hcomp := SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex
        (lastImageLE a s)
      rw [hcomp]
      exact (map_faceOfLE
        ((imageChain a s).monotone (Fin.le_last j))).trans rfl)
    (w := by
      intro i hi
      subsingleton)

private noncomputable def isColimitNondegenerateNerveCocone
    (X : SSet.{u}) [X.Nonsingular] :
    IsColimit (SSet.nondegenerateNerve.mapCocone X.coconeN') := by
  apply evaluationJointlyReflectsColimits
  rintro ⟨⟨d⟩⟩
  let G := X.functorN' ⋙ SSet.nondegenerateNerve
  let c := SSet.nondegenerateNerve.mapCocone X.coconeN'
  let ev := (evaluation SimplexCategoryᵒᵖ (Type u)).obj (op ⦋d⦌)
  let Gd := G ⋙ ev
  let ce := ev.mapCocone c
  let ct := Gd.coconeTypesEquiv.symm ce
  apply Nonempty.some
  apply (Types.isColimit_iff_coconeTypesIsColimit ce).2
  refine ⟨⟨?_, ?_⟩⟩
  · intro q₁ q₂ hq
    obtain ⟨a, s, rfl⟩ := Functor.ιColimitType_jointly_surjective Gd q₁
    obtain ⟨b, t, rfl⟩ := Functor.ιColimitType_jointly_surjective Gd q₂
    change imageChain a s = imageChain b t at hq
    let rep : (SSet.nondegenerateNerve.obj X) _⦋d⦌ → Gd.ColimitType :=
      fun z => Gd.ιColimitType (z.obj (Fin.last d)) (liftChain z)
    have hrep (a : X.N) (s : Gd.obj a) :
        Gd.ιColimitType a s = rep (imageChain a s) := by
      let k := (imageChain a s).obj (Fin.last d)
      let hka : k ≤ a := lastImageLE a s
      let w := liftChain (imageChain a s)
      calc
        Gd.ιColimitType a s =
            Gd.ιColimitType a (Gd.map (homOfLE hka) w) := by
          congr 1
          change s =
            (SSet.nondegenerateNerve.map
              (SSet.stdSimplex.map (SSet.N.monoOfLE hka))).app _ w
          exact (map_liftChain_to_stage a s).symm
        _ = Gd.ιColimitType k w :=
          Gd.ιColimitType_map (homOfLE hka) w
        _ = rep (imageChain a s) := rfl
    exact (hrep a s).trans ((congrArg rep hq).trans (hrep b t).symm)
  · rw [Functor.CoconeTypes.descColimitType_surjective_iff]
    intro z
    change (SSet.nondegenerateNerve.obj X) _⦋d⦌ at z
    let k := z.obj (Fin.last d)
    refine ⟨k, liftChain (X := X) z, ?_⟩
    change (SSet.nondegenerateNerve.map
      (SSet.yonedaEquiv.symm k.simplex)).app _
        (liftChain (X := X) z) = z
    exact map_liftChain (X := X) z

set_option linter.unnecessarySimpa false in
private noncomputable def faceDiagramIso
    (X : SSet.{u}) [X.Nonsingular] :
    X.functorN' ⋙ SSet.sd ≅
      X.functorN' ⋙ SSet.nondegenerateNerve :=
  NatIso.ofComponents
    (fun a => by
      letI : IsIso
          (SSet.sdToNondegenerateNerve.app (X.functorN'.obj a)) := by
        change IsIso (SSet.sdToNondegenerateNerve.app
          (SSet.stdSimplex.obj ⦋a.dim⦌))
        exact sdToNondegenerateNerve_stdSimplex_app_isIso ⦋a.dim⦌
      exact asIso
        (SSet.sdToNondegenerateNerve.app (X.functorN'.obj a)))
    (fun f => by
      simpa using SSet.sdToNondegenerateNerve.naturality
        (X.functorN'.map f))

private theorem sdToNondegenerateNerve_app_isIso
    (X : SSet.{u}) [X.Nonsingular] :
    IsIso (SSet.sdToNondegenerateNerve.app X) := by
  let cSd := SSet.sd.mapCocone X.coconeN'
  let cN := SSet.nondegenerateNerve.mapCocone X.coconeN'
  let e := faceDiagramIso X
  let hSd : IsColimit cSd :=
    isColimitOfPreserves SSet.sd X.isColimitCoconeN'
  let hN : IsColimit cN := isColimitNondegenerateNerveCocone X
  let hPre : IsColimit ((Cocone.precompose e.hom).obj cN) :=
    (IsColimit.precomposeHomEquiv e cN).symm hN
  let eApex := hSd.coconePointUniqueUpToIso hPre
  have heq : eApex.hom = SSet.sdToNondegenerateNerve.app X := by
    apply hSd.hom_ext
    intro a
    rw [hSd.comp_coconePointUniqueUpToIso_hom hPre]
    change SSet.sdToNondegenerateNerve.app (X.functorN'.obj a) ≫
        SSet.nondegenerateNerve.map (X.coconeN'.ι.app a) =
      SSet.sd.map (X.coconeN'.ι.app a) ≫
        SSet.sdToNondegenerateNerve.app X
    exact (SSet.sdToNondegenerateNerve.naturality
      (X.coconeN'.ι.app a)).symm
  exact heq ▸ (inferInstance : IsIso eApex.hom)

/-- For a nonsingular simplicial set, subdivision is the nerve of its ordered
type of nondegenerate simplices. -/
@[no_expose]
noncomputable def sdIsoNondegenerateNerve
    (X : SSet.{u}) [X.Nonsingular] :
    SSet.sd.obj X ≅ SSet.nondegenerateNerve.obj X := by
  let _ : IsIso (SSet.sdToNondegenerateNerve.app X) :=
    sdToNondegenerateNerve_app_isIso X
  exact asIso (SSet.sdToNondegenerateNerve.app X)

/-- The public subdivision/nondegenerate-nerve isomorphism uses the natural
comparison as its forward map. -/
@[simp]
theorem sdIsoNondegenerateNerve_hom
    (X : SSet.{u}) [X.Nonsingular] :
    (SSet.sdIsoNondegenerateNerve X).hom =
      SSet.sdToNondegenerateNerve.app X := by
  let _ : IsIso (SSet.sdToNondegenerateNerve.app X) :=
    sdToNondegenerateNerve_app_isIso X
  exact CategoryTheory.asIso_hom
    (SSet.sdToNondegenerateNerve.app X)

set_option linter.style.haveILetI false in
instance (X : SSet.{u}) [X.Nonsingular] :
    (SSet.sd.obj X).Nonsingular := by
  haveI : (SSet.nondegenerateNerve.obj X).Nonsingular := by
    change (CategoryTheory.nerve (SSet.N.functor.obj X)).Nonsingular
    infer_instance
  exact SSet.Nonsingular.of_iso (SSet.sdIsoNondegenerateNerve X).symm

set_option linter.style.haveILetI false in
instance (X : SSet.{u}) [X.Nonsingular] (k : ℕ) :
    ((SSet.sdIter k).obj X).Nonsingular := by
  induction k with
  | zero => simpa
  | succ k ih =>
      rw [SSet.sdIter_obj_succ]
      letI : ((SSet.sdIter k).obj X).Nonsingular := ih
      infer_instance

end SSet
