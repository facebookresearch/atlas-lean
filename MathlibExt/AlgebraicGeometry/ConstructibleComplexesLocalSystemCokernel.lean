/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes

import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Cokernels of finite-rank local systems

Cokernels of morphisms of finite-rank local systems are finite-rank local systems.
Sources: Dimca, *Sheaves in Topology*, Chapters 2–4; de Cataldo–Migliorini,
https://arxiv.org/abs/0712.0349, §1.5.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ComplexAnalytification
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes

attribute [local instance] HasDerivedCategory.standard

private def constantRestriction (k : Type) [Field k] {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : Topology.IsOpenEmbedding f) (V : ModuleCat.{0} k) :
    (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k)).obj V ⟶
      (hf.sheafPullback (ModuleCat.{0} k)).obj
        ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} k)).obj V) :=
  ⟨sheafifyLift _ (Functor.whiskerLeft hf.functor.op
    (toSheafify _ ((Functor.const (Opens Y)ᵒᵖ).obj V)))
      ((hf.sheafPullback (ModuleCat.{0} k)).obj _).property⟩

private theorem constantRestriction_isIso (k : Type) [Field k] {X Y : TopCat.{0}}
    (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) (V : ModuleCat.{0} k) :
    IsIso (constantRestriction k f hf V) := by
  let P := (Functor.const (Opens Y)ᵒᵖ).obj V
  let H := (Functor.whiskeringLeft _ _ (ModuleCat.{0} k)).obj hf.functor.op
  have h := Functor.W_map_of_adjunction_of_isContinuous (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X) (Opens.map f) H
    (hf.isOpenMap.adjunction.op.whiskerLeft (ModuleCat.{0} k))
    (toSheafify (Opens.grothendieckTopology Y) P)
    ((Opens.grothendieckTopology Y).W_toSheafify P)
  have hmap : IsIso ((presheafToSheaf (Opens.grothendieckTopology X)
      (ModuleCat.{0} k)).map (H.map (toSheafify _ P))) :=
    ((Opens.grothendieckTopology X).W_iff _).mp h
  let Q := (hf.sheafPullback (ModuleCat.{0} k)).obj
    ((constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} k)).obj V)
  have he : constantRestriction k f hf V =
      (presheafToSheaf (Opens.grothendieckTopology X)
        (ModuleCat.{0} k)).map (H.map (toSheafify _ P)) ≫
        (sheafificationAdjunction _ (ModuleCat.{0} k)).counit.app Q := by
    apply Sheaf.hom_ext
    change sheafifyLift _ _ _ = sheafifyMap _ _ ≫
      ((sheafificationAdjunction _ (ModuleCat.{0} k)).counit.app Q).hom
    rw [sheafificationAdjunction_counit_app_val]
    calc
      _ = sheafifyLift _ (H.map (toSheafify _ P) ≫ 𝟙 Q.obj) Q.property :=
        congrArg (fun η => sheafifyLift _ η Q.property) (Category.comp_id _).symm
      _ = _ := (sheafifyMap_sheafifyLift _ _ _ _).symm
  have hcounit : IsIso ((sheafificationAdjunction (Opens.grothendieckTopology X)
    (ModuleCat.{0} k)).counit.app Q) := inferInstance
  rw [he]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hmap hcounit

private def restrictionComp (k : Type) [Field k] {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)
    (g : Y ⟶ Z) (hg : Topology.IsOpenEmbedding g) (F : CoefficientSheaf k Z) :
    (hf.sheafPullback (ModuleCat.{0} k)).obj
      ((hg.sheafPullback (ModuleCat.{0} k)).obj F) ≅
    ((hg.comp hf).sheafPullback (f := f ≫ g) (ModuleCat.{0} k)).obj F := by
  have hfg : Topology.IsOpenEmbedding (f ≫ g) := hg.comp hf
  let e : hf.functor ⋙ hg.functor ≅ hfg.functor :=
    NatIso.ofComponents (fun U => eqToIso (Opens.ext (Set.image_image g f U)))
  exact (fullyFaithfulSheafToPresheaf _ _).preimageIso
    ((Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (NatIso.op e.symm) F.obj)

private def restrictionCongr (k : Type) [Field k] {X Y : TopCat.{0}}
    (f g : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) (hg : Topology.IsOpenEmbedding g)
    (h : f = g) (F : CoefficientSheaf k Y) :
    (hf.sheafPullback (ModuleCat.{0} k)).obj F ≅
      (hg.sheafPullback (ModuleCat.{0} k)).obj F := by
  subst g
  exact Iso.refl _

private def restrictionOfLE (k : Type) [Field k] (Z : TopCat.{0})
    (U B : Opens Z) (h : B ≤ U) (F : CoefficientSheaf k Z) :
    let f : TopCat.of B ⟶ TopCat.of U := (Opens.toTopCat Z).map (homOfLE h)
    let hf : Topology.IsOpenEmbedding f :=
      U.isOpenEmbedding.of_comp f B.isOpenEmbedding
    (hf.sheafPullback (ModuleCat.{0} k)).obj
      ((U.sheafRestrict (C := ModuleCat.{0} k)).obj F) ≅
      (B.sheafRestrict (C := ModuleCat.{0} k)).obj F :=
  restrictionComp k _ _ U.inclusion' U.isOpenEmbedding F

private theorem trivialization_of_embedding (k : Type) [Field k] (Z : TopCat.{0})
    (F : CoefficientSheaf k Z) {X : TopCat.{0}} (f : X ⟶ Z)
    (hf : Topology.IsOpenEmbedding f) (y : X) (V : ModuleCat.{0} k)
    [FiniteDimensional k V]
    (i : (hf.sheafPullback (ModuleCat.{0} k)).obj F ≅
      (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k)).obj V) :
    ∃ U : Opens Z, f y ∈ U ∧ ∃ V : ModuleCat.{0} k, FiniteDimensional k V ∧
      Nonempty ((TopCat.Sheaf.pullback (ModuleCat.{0} k) U.inclusion').obj F ≅
        (constantSheaf (Opens.grothendieckTopology (TopCat.of U))
          (ModuleCat.{0} k)).obj V) := by
  let U : Opens Z := ⟨Set.range f, hf.isOpen_range⟩
  let e : X ≅ TopCat.of U := TopCat.isoOfHomeo hf.toIsEmbedding.toHomeomorph
  have he : e.inv ≫ f = U.inclusion' := by
    apply TopCat.ext
    intro z
    exact congrArg Subtype.val (hf.toIsEmbedding.toHomeomorph.apply_symm_apply z)
  have hinv : Topology.IsOpenEmbedding e.inv := (TopCat.homeoOfIso e).symm.isOpenEmbedding
  have hc : IsIso (constantRestriction k e.inv hinv V) := constantRestriction_isIso _ _ _ _
  let j := (restrictionComp k e.inv hinv f hf F).symm ≪≫
    (hinv.sheafPullback (ModuleCat.{0} k)).mapIso i ≪≫
      (asIso (constantRestriction k e.inv hinv V)).symm
  have j' : (U.sheafRestrict (C := ModuleCat.{0} k)).obj F ≅
      (constantSheaf (Opens.grothendieckTopology (TopCat.of U)) (ModuleCat.{0} k)).obj V := by
    exact (restrictionCongr k (e.inv ≫ f) U.inclusion' (hf.comp hinv)
      U.isOpenEmbedding he F).symm ≪≫ j
  refine ⟨U, ⟨y, rfl⟩, V, inferInstance, ⟨?_⟩⟩
  exact (U.isOpenEmbedding.sheafPullbackIso (ModuleCat.{0} k)).app F ≪≫ j'

private abbrev restr (k : Type) [Field k] (Z : TopCat.{0}) (U : Opens Z) :=
  U.sheafRestrict (C := ModuleCat.{0} k)

private def openFunctor (Z : TopCat.{0}) (U : Opens Z) : Opens U ⥤ Opens Z :=
  U.isOpenEmbedding.functor

private def constRestr (k : Type) [Field k] (Z : TopCat.{0}) (U : Opens Z)
    (V : ModuleCat.{0} k) :
    (constantSheaf (Opens.grothendieckTopology U) (ModuleCat.{0} k)).obj V ⟶
      (restr k Z U).obj ((constantSheaf (Opens.grothendieckTopology Z)
        (ModuleCat.{0} k)).obj V) :=
  let E := openFunctor Z U
  ⟨sheafifyLift _ (Functor.whiskerLeft E.op
    (toSheafify _ ((Functor.const (Opens Z)ᵒᵖ).obj V)))
    ((restr k Z U).obj _).property⟩

private theorem constRestr_isIso (k : Type) [Field k] (Z : TopCat.{0}) (U : Opens Z)
    (V : ModuleCat.{0} k) : IsIso (constRestr k Z U V) :=
  constantRestriction_isIso k (U.inclusion' : TopCat.of U ⟶ Z) U.isOpenEmbedding V

private abbrev cs (k : Type) [Field k] (Z : TopCat.{0}) :=
  constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k)

private abbrev cu (k : Type) [Field k] (Z : TopCat.{0}) (V : ModuleCat.{0} k) :=
  toSheafify (Opens.grothendieckTopology Z) ((Functor.const (Opens Z)ᵒᵖ).obj V)

private theorem cu_res (k : Type) [Field k] (Z : TopCat.{0}) (V : ModuleCat.{0} k)
    (U B : Opens Z) (j : B ⟶ U) :
    (cu k Z V).app (op U) ≫ ((cs k Z).obj V).obj.map j.op =
      (cu k Z V).app (op B) := by
  calc
    _ = 𝟙 V ≫ (cu k Z V).app (op B) := ((cu k Z V).naturality j.op).symm
    _ = _ := Category.id_comp _

private theorem cu_map (k : Type) [Field k] (Z : TopCat.{0})
    (V W : ModuleCat.{0} k) (g : V ⟶ W) :
    cu k Z V ≫ ((cs k Z).map g).hom =
      (Functor.const (Opens Z)ᵒᵖ).map g ≫ cu k Z W :=
  (toSheafify_naturality _ _).symm

private theorem constRestr_unit (k : Type) [Field k] (Z : TopCat.{0}) (U : Opens Z)
    (V : ModuleCat.{0} k) :
    cu k (TopCat.of U) V ≫ (constRestr k Z U V).hom =
      Functor.whiskerLeft (openFunctor Z U).op (cu k Z V) := by
  exact toSheafify_sheafifyLift _ _ _

private theorem constant_map_locally (k : Type) [Field k] (Z : TopCat.{0})
    (V W : ModuleCat.{0} k) [FiniteDimensional k V]
    (a : (cs k Z).obj V ⟶ (cs k Z).obj W) (x : Z) :
    ∃ U : Opens Z, x ∈ U ∧ ∃ g : V ⟶ W,
      (cs k (TopCat.of U)).map g ≫ constRestr k Z U W =
        constRestr k Z U V ≫ (restr k Z U).map a := by
  classical
  let b := Module.finBasis k V
  let t : V ⟶ ((cs k Z).obj W).obj.obj (op (⊤ : Opens Z)) :=
    (cu k Z V).app _ ≫ a.hom.app _
  have hs (i : Fin (Module.finrank k V)) :
      ∃ N : Opens Z, x ∈ N ∧ ∃ w : W,
        (cu k Z W).app (op N) w =
          ((cs k Z).obj W).obj.map (homOfLE (le_top : N ≤ ⊤)).op (t (b i)) := by
    obtain ⟨N, hN, ⟨w, hw⟩, hx⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff (cu k Z W)).mp inferInstance
        ⊤ (t (b i)) x (by trivial)
    exact ⟨N, hx, w, hw⟩
  choose N hx w hw using hs
  let U : Opens Z := ⨅ i, N i
  have hU : x ∈ U := by
    simpa only [U, ← SetLike.mem_coe, Opens.coe_iInf, Set.mem_iInter] using hx
  let g : V ⟶ W := ModuleCat.ofHom (b.constr k w)
  have he : (cu k Z V).app (op U) ≫ a.hom.app (op U) =
      g ≫ (cu k Z W).app (op U) := by
    apply ModuleCat.hom_ext
    apply b.ext
    intro i
    let j : U ⟶ N i := homOfLE (iInf_le N i)
    have h := congrArg (((cs k Z).obj W).obj.map j.op) (hw i)
    have hnV := congrArg (fun f : V ⟶ ((cs k Z).obj V).obj.obj (op U) => f (b i))
      (cu_res k Z V ⊤ U (homOfLE le_top))
    have hnW := congrArg (fun f : W ⟶ ((cs k Z).obj W).obj.obj (op U) => f (w i))
      (cu_res k Z W (N i) U j)
    have ha := a.hom.naturality_apply (homOfLE (le_top : U ≤ ⊤)).op
      ((cu k Z V).app (op ⊤) (b i))
    simp only [ConcreteCategory.comp_apply] at hnV hnW
    simp only [t, ConcreteCategory.comp_apply] at h
    rw [← Functor.map_comp_apply] at h
    change _ = ((cs k Z).obj W).obj.map (homOfLE (le_top : U ≤ ⊤)).op
      (a.hom.app (op ⊤) ((cu k Z V).app (op ⊤) (b i))) at h
    rw [← ha] at h
    change a.hom.app (op U) ((cu k Z V).app (op U) (b i)) =
      (cu k Z W).app (op U) ((b.constr k w) (b i))
    rw [Module.Basis.constr_basis]
    exact (congrArg (a.hom.app (op U)) hnV.symm).trans (h.symm.trans hnW)
  refine ⟨U, hU, g, ?_⟩
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _ ((restr k Z U).obj ((cs k Z).obj W)).property
  change cu k (TopCat.of U) V ≫ ((cs k (TopCat.of U)).map g).hom ≫
      (constRestr k Z U W).hom =
    cu k (TopCat.of U) V ≫ (constRestr k Z U V).hom ≫ _
  rw [← Category.assoc, cu_map, Category.assoc, constRestr_unit,
    ← Category.assoc, constRestr_unit]
  apply NatTrans.ext
  funext O
  let B : Opens Z := (openFunctor Z U).obj O.unop
  let j : B ⟶ U := homOfLE (by
    rintro y ⟨z, hz, rfl⟩
    exact z.property)
  have h := congrArg (fun f => f ≫ ((cs k Z).obj W).obj.map j.op) he
  change g ≫ (cu k Z W).app (op B) = (cu k Z V).app (op B) ≫ a.hom.app (op B)
  calc
    _ = (g ≫ (cu k Z W).app (op U)) ≫ ((cs k Z).obj W).obj.map j.op := by
      rw [Category.assoc, cu_res]
    _ = ((cu k Z V).app (op U) ≫ a.hom.app (op U)) ≫
        ((cs k Z).obj W).obj.map j.op := h.symm
    _ = _ := by rw [Category.assoc, ← a.hom.naturality j.op, ← Category.assoc, cu_res]

private instance restriction_preservesFiniteColimits (k : Type) [Field k]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) :
    PreservesFiniteColimits (hf.sheafPullback (ModuleCat.{0} k)) :=
  preservesFiniteColimits_of_natIso (hf.sheafPullbackIso (ModuleCat.{0} k))

private instance restriction_additive (k : Type) [Field k]
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) :
    (hf.sheafPullback (ModuleCat.{0} k)).Additive where
  map_add := by intro F G a b; rfl

private instance constant_preservesFiniteColimits (k : Type) [Field k] (Z : TopCat.{0}) :
    PreservesFiniteColimits (cs k Z) := by
  have : (cs k Z).IsLeftAdjoint :=
    (constantSheafAdj (Opens.grothendieckTopology Z) (ModuleCat.{0} k)
      (isTerminalTop (α := Opens Z))).isLeftAdjoint
  infer_instance

private theorem constant_cokernel_local (k : Type) [Field k] (Z : TopCat.{0})
    (V W : ModuleCat.{0} k) [FiniteDimensional k V] [FiniteDimensional k W]
    (a : (cs k Z).obj V ⟶ (cs k Z).obj W) (x : Z) :
    ∃ U : Opens Z, x ∈ U ∧ ∃ Q : ModuleCat.{0} k, FiniteDimensional k Q ∧
      Nonempty ((restr k Z U).obj (cokernel a) ≅ (cs k (TopCat.of U)).obj Q) := by
  obtain ⟨U, hx, g, hg⟩ := constant_map_locally k Z V W a x
  have hV : IsIso (constRestr k Z U V) := constRestr_isIso k Z U V
  have hW : IsIso (constRestr k Z U W) := constRestr_isIso k Z U W
  have : FiniteDimensional k (cokernel g : ModuleCat.{0} k) :=
    Module.Finite.of_surjective (cokernel.π g).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  have : PreservesFiniteColimits (restr k Z U) :=
    restriction_preservesFiniteColimits k (U.inclusion' : TopCat.of U ⟶ Z) U.isOpenEmbedding
  have : (restr k Z U).Additive :=
    restriction_additive k (U.inclusion' : TopCat.of U ⟶ Z) U.isOpenEmbedding
  have : PreservesFiniteColimits (cs k (TopCat.of U)) :=
    constant_preservesFiniteColimits k (TopCat.of U)
  refine ⟨U, hx, cokernel g, inferInstance, ⟨?_⟩⟩
  exact PreservesCokernel.iso (restr k Z U) a ≪≫
    (cokernel.mapIso (f := (cs k (TopCat.of U)).map g) ((restr k Z U).map a)
      (asIso (constRestr k Z U V)) (asIso (constRestr k Z U W)) hg).symm ≪≫
    (PreservesCokernel.iso (cs k (TopCat.of U)) g).symm

private def smallerTrivialization (k : Type) [Field k] (Z : TopCat.{0})
    (U B : Opens Z) (h : B ≤ U) (F : CoefficientSheaf k Z) (V : ModuleCat.{0} k)
    (i : (restr k Z U).obj F ≅ (cs k (TopCat.of U)).obj V) :
    (restr k Z B).obj F ≅ (cs k (TopCat.of B)).obj V := by
  let f : TopCat.of B ⟶ TopCat.of U := (Opens.toTopCat Z).map (homOfLE h)
  have hf : Topology.IsOpenEmbedding f := U.isOpenEmbedding.of_comp f B.isOpenEmbedding
  have : IsIso (constantRestriction k f hf V) := constantRestriction_isIso k f hf V
  exact (restrictionOfLE k Z U B h F).symm ≪≫
    (hf.sheafPullback (ModuleCat.{0} k)).mapIso i ≪≫
    (asIso (constantRestriction k f hf V)).symm

/-- Cokernels of such morphisms remain finite-rank local systems. -/
public theorem localSystem_cokernel (k : Type) [Field k] (Z : TopCat.{0})
    (F G : CoefficientSheaf k Z) (a : F ⟶ G)
    (hF : ConstructibleComplexes.IsFiniteRankLocalSystem k Z F)
    (hG : ConstructibleComplexes.IsFiniteRankLocalSystem k Z G) :
    ConstructibleComplexes.IsFiniteRankLocalSystem k Z (cokernel a)
    := by
  intro x
  obtain ⟨U, hxU, V, hV, ⟨iF⟩⟩ := hF x
  obtain ⟨W, hxW, Q, hQ, ⟨iG⟩⟩ := hG x
  let S : Opens Z := U ⊓ W
  have hxS : x ∈ S := ⟨hxU, hxW⟩
  let eF : (restr k Z S).obj F ≅ (cs k (TopCat.of S)).obj V :=
    smallerTrivialization k Z U S inf_le_left F V
      (((U.isOpenEmbedding.sheafPullbackIso (ModuleCat.{0} k)).app F).symm ≪≫ iF)
  let eG : (restr k Z S).obj G ≅ (cs k (TopCat.of S)).obj Q :=
    smallerTrivialization k Z W S inf_le_right G Q
      (((W.isOpenEmbedding.sheafPullbackIso (ModuleCat.{0} k)).app G).symm ≪≫ iG)
  have : PreservesFiniteColimits (restr k Z S) :=
    restriction_preservesFiniteColimits k (S.inclusion' : TopCat.of S ⟶ Z) S.isOpenEmbedding
  have : (restr k Z S).Additive :=
    restriction_additive k (S.inclusion' : TopCat.of S ⟶ Z) S.isOpenEmbedding
  let b : (cs k (TopCat.of S)).obj V ⟶ (cs k (TopCat.of S)).obj Q :=
    eF.inv ≫ (restr k Z S).map a ≫ eG.hom
  let e : (restr k Z S).obj (cokernel a) ≅ cokernel b :=
    PreservesCokernel.iso (restr k Z S) a ≪≫
      cokernel.mapIso (f := (restr k Z S).map a) b eF eG (by simp [b])
  obtain ⟨B, hxB, R, hR, ⟨i⟩⟩ := constant_cokernel_local k (TopCat.of S) V Q b ⟨x, hxS⟩
  let f : TopCat.of B ⟶ Z := B.inclusion' ≫ S.inclusion'
  have hf : Topology.IsOpenEmbedding f := S.isOpenEmbedding.comp B.isOpenEmbedding
  let j : (hf.sheafPullback (ModuleCat.{0} k)).obj (cokernel a) ≅
      (cs k (TopCat.of B)).obj R :=
    (restrictionComp k B.inclusion' B.isOpenEmbedding S.inclusion' S.isOpenEmbedding
      (cokernel a)).symm ≪≫ (restr k (TopCat.of S) B).mapIso e ≪≫ i
  exact trivialization_of_embedding k Z (cokernel a) f hf ⟨⟨x, hxS⟩, hxB⟩ R j

end WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted
