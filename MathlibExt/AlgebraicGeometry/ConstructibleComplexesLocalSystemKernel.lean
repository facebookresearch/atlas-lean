/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ConstructibleComplexes

import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Kernels of finite-rank local systems

Kernels of morphisms of finite-rank local systems are finite-rank local systems.

Sources: Dimca, *Sheaves in Topology*, Chapters 2–4; de Cataldo–Migliorini,
https://arxiv.org/abs/0712.0349, §1.5.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted

open CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ConstructibleComplexes
open CategoryTheory.Functor TopologicalSpace Opposite

private def pullbackComp (k : Type) [Field k] {X Y Z : TopCat.{0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    TopCat.Sheaf.pullback (ModuleCat.{0} k) g ⋙ TopCat.Sheaf.pullback (ModuleCat.{0} k) f ≅
      TopCat.Sheaf.pullback (ModuleCat.{0} k) (f ≫ g) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) g).comp
    (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f)).leftAdjointUniq
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) (f ≫ g))

private def constantPullback (k : Type) [Field k] {X Y : TopCat.{0}} (f : X ⟶ Y) :
    constantSheaf (Opens.grothendieckTopology Y) (ModuleCat.{0} k) ⋙
      TopCat.Sheaf.pullback (ModuleCat.{0} k) f ≅
        constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} k) :=
  ((constantSheafAdj (Opens.grothendieckTopology Y) (ModuleCat.{0} k)
    (isTerminalTop (α := Opens Y))).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction (ModuleCat.{0} k) f)).leftAdjointUniq
        (constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{0} k)
          (isTerminalTop (α := Opens X)))

private theorem openEmbedding_cocontinuous {X Y : TopCat.{0}} (f : X ⟶ Y)
    (hf : Topology.IsOpenEmbedding f) :
    hf.functor.IsCocontinuous (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) :=
  (hf.isOpenMap.adjunction.isCocontinuous_iff_coverPreserving _ _).mpr
    (coverPreserving_opens_map f)

private def restrictionConstantIso (k : Type) [Field k] (Z : TopCat.{0})
    (U : Opens Z) (V : ModuleCat.{0} k) :
    (constantSheaf (Opens.grothendieckTopology (TopCat.of U)) (ModuleCat.{0} k)).obj V ≅
      (U.sheafRestrict.obj
        ((constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k)).obj V)) := by
  let J := Opens.grothendieckTopology (TopCat.of U)
  let H : Opens U ⥤ Opens Z := U.isOpenEmbedding.functor
  let P := (Functor.const (Opens Z)ᵒᵖ).obj V
  let η := whiskerLeft H.op (toSheafify (Opens.grothendieckTopology Z) P)
  letI : H.IsCocontinuous J (Opens.grothendieckTopology Z) :=
    openEmbedding_cocontinuous U.inclusion' U.isOpenEmbedding
  letI hηi : Presheaf.IsLocallyInjective J η :=
    Presheaf.isLocallyInjective_whisker J (Opens.grothendieckTopology Z)
      H (toSheafify (Opens.grothendieckTopology Z) P)
  letI hηs : Presheaf.IsLocallySurjective J η :=
    Presheaf.isLocallySurjective_whisker J (Opens.grothendieckTopology Z)
      H (toSheafify (Opens.grothendieckTopology Z) P)
  let t : (constantSheaf J (ModuleCat.{0} k)).obj V ⟶ U.sheafRestrict.obj
      ((constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k)).obj V) :=
    ⟨sheafifyLift J η (U.sheafRestrict.obj
      ((constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k)).obj V)).property⟩
  have ht : toSheafify J ((Functor.const (Opens U)ᵒᵖ).obj V) ≫ t.hom = η := by
    exact toSheafify_sheafifyLift _ _ _
  letI : Presheaf.IsLocallyInjective J t.hom := by
    apply (Presheaf.comp_isLocallyInjective_iff J
      (toSheafify J ((Functor.const (Opens U)ᵒᵖ).obj V)) t.hom).mp
    rw [ht]
    exact hηi
  letI : Presheaf.IsLocallySurjective J t.hom := by
    apply (Presheaf.comp_isLocallySurjective_iff J
      (toSheafify J ((Functor.const (Opens U)ᵒᵖ).obj V)) t.hom).mp
    rw [ht]
    exact hηs
  letI : IsIso t := (Sheaf.isLocallyBijective_iff_isIso t).mp ⟨inferInstance, inferInstance⟩
  exact asIso t

private theorem restrictionConstantIso_unit (k : Type) [Field k] (Z : TopCat.{0})
    (U : Opens Z) (V : ModuleCat.{0} k) :
    toSheafify (Opens.grothendieckTopology (TopCat.of U))
        ((Functor.const (Opens U)ᵒᵖ).obj V) ≫
      (restrictionConstantIso k Z U V).hom.hom =
        whiskerLeft U.isOpenEmbedding.functor.op
          (toSheafify (Opens.grothendieckTopology Z) ((Functor.const (Opens Z)ᵒᵖ).obj V)) := by
  dsimp only [restrictionConstantIso, asIso]
  exact toSheafify_sheafifyLift _ _ _

private theorem constant_morphism_local (k : Type) [Field k] (Z : TopCat.{0})
    (V W : ModuleCat.{0} k) [FiniteDimensional k V]
    (a : (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k)).obj V ⟶
      (constantSheaf (Opens.grothendieckTopology Z) (ModuleCat.{0} k)).obj W) (x : Z) :
    ∃ U : Opens Z, x ∈ U ∧ ∃ d : V ⟶ W,
      (constantSheaf (Opens.grothendieckTopology (TopCat.of U)) (ModuleCat.{0} k)).map d ≫
        (restrictionConstantIso k Z U W).hom =
          (restrictionConstantIso k Z U V).hom ≫ U.sheafRestrict.map a := by
  classical
  let J := Opens.grothendieckTopology Z
  let PV := (Functor.const (Opens Z)ᵒᵖ).obj V
  let PW := (Functor.const (Opens Z)ᵒᵖ).obj W
  let b := toSheafify J PV ≫ a.hom
  let B := Module.finBasis k V
  have h (i : Fin (Module.finrank k V)) : ∃ U : Opens Z, x ∈ U ∧
      ∃ w : W, (toSheafify J PW).app (op U) w = b.app (op U) (B i) := by
    obtain ⟨U, f, ⟨w, hw⟩, hx⟩ :=
      Presheaf.imageSieve_mem J (toSheafify J PW) (b.app (op ⊤) (B i)) x trivial
    refine ⟨U, hx, w, ?_⟩
    rw [hw]
    exact (NatTrans.naturality_apply b f.op (B i)).symm
  choose Us hx ws hw using h
  let U : Opens Z := ⨅ i, Us i
  have hU (i) : U ≤ Us i := iInf_le Us i
  refine ⟨U, ?_, ModuleCat.ofHom (B.constr k ws), ?_⟩
  · change x ∈ (U : Set Z)
    simp only [U, Opens.coe_iInf, Set.mem_iInter]
    exact hx
  · apply Sheaf.hom_ext
    apply sheafify_hom_ext _ _ _
      (U.sheafRestrict.obj ((constantSheaf J (ModuleCat.{0} k)).obj W)).property
    change toSheafify (Opens.grothendieckTopology U) ((Functor.const (Opens U)ᵒᵖ).obj V) ≫
      sheafifyMap (Opens.grothendieckTopology U)
        ((Functor.const (Opens U)ᵒᵖ).map (ModuleCat.ofHom (B.constr k ws))) ≫
          (restrictionConstantIso k Z U W).hom.hom = _
    rw [← toSheafify_naturality_assoc]
    rw [restrictionConstantIso_unit]
    change _ = toSheafify (Opens.grothendieckTopology U) _ ≫
      (restrictionConstantIso k Z U V).hom.hom ≫ (U.sheafRestrict.map a).hom
    rw [← Category.assoc, restrictionConstantIso_unit]
    apply NatTrans.ext
    funext O
    apply ModuleCat.hom_ext
    apply B.ext
    intro i
    change (toSheafify J PW).app (op (U.isOpenEmbedding.functor.obj O.unop))
        ((B.constr k ws) (B i)) = b.app (op (U.isOpenEmbedding.functor.obj O.unop)) (B i)
    rw [B.constr_basis]
    let f : U.isOpenEmbedding.functor.obj O.unop ⟶ Us i :=
      homOfLE ((U.isOpenEmbedding.functor.map (homOfLE le_top)).le.trans
        (by simpa using hU i))
    have hη := NatTrans.naturality_apply (toSheafify J PW) f.op (ws i)
    have hb := NatTrans.naturality_apply b f.op (B i)
    exact hη.trans ((congrArg (fun s ↦ (sheafify J PW).map f.op s) (hw i)).trans hb.symm)

private def refineModel (k : Type) [Field k] (Z : TopCat.{0})
    (F : CoefficientSheaf k Z) (U V : Opens Z) (hVU : V ≤ U) (A : ModuleCat.{0} k)
    (e : (TopCat.Sheaf.pullback (ModuleCat.{0} k) (PerverseSheaves.openInclusion Z U)).obj F ≅
      (constantSheaf (Opens.grothendieckTopology (TopCat.of U)) (ModuleCat.{0} k)).obj A) :
    (TopCat.Sheaf.pullback (ModuleCat.{0} k) (PerverseSheaves.openInclusion Z V)).obj F ≅
      (constantSheaf (Opens.grothendieckTopology (TopCat.of V)) (ModuleCat.{0} k)).obj A := by
  let f : TopCat.of V ⟶ TopCat.of U := (Opens.toTopCat Z).map (homOfLE hVU)
  have hf : f ≫ PerverseSheaves.openInclusion Z U = PerverseSheaves.openInclusion Z V := rfl
  exact (eqToIso (congrArg (fun g ↦ (TopCat.Sheaf.pullback (ModuleCat.{0} k) g).obj F) hf)).symm ≪≫
      ((pullbackComp k f (PerverseSheaves.openInclusion Z U)).app F).symm ≪≫
        (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).mapIso e ≪≫
          (constantPullback k f).app A

private theorem nestedModel (k : Type) [Field k] (Z : TopCat.{0})
    (F : CoefficientSheaf k Z) (U : Opens Z) (x : U) (V : Opens U) (hx : x ∈ V)
    (A : ModuleCat.{0} k)
    (i : (TopCat.Sheaf.pullback (ModuleCat.{0} k)
        (PerverseSheaves.openInclusion (TopCat.of U) V)).obj
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) U.inclusion').obj F) ≅
        (constantSheaf (Opens.grothendieckTopology (TopCat.of V)) (ModuleCat.{0} k)).obj A) :
    ∃ W : Opens Z, x.val ∈ W ∧ Nonempty
      ((TopCat.Sheaf.pullback (ModuleCat.{0} k) W.inclusion').obj F ≅
        (constantSheaf (Opens.grothendieckTopology (TopCat.of W)) (ModuleCat.{0} k)).obj A) := by
  let W := U.isOpenEmbedding.functor.obj V
  let e : TopCat.of V ≅ TopCat.of W :=
    TopCat.isoOfHomeo (U.isOpenEmbedding.isEmbedding.homeomorphImage (V : Set U))
  let g : TopCat.of V ⟶ Z := (PerverseSheaves.openInclusion (TopCat.of U) V) ≫ U.inclusion'
  have hg : e.hom ≫ W.inclusion' = g := rfl
  have hginv : e.inv ≫ g = W.inclusion' := by
    rw [← hg]
    exact e.inv_hom_id_assoc _
  refine ⟨W, ⟨x, hx, rfl⟩, ⟨?_⟩⟩
  exact (eqToIso (congrArg (fun f ↦ (TopCat.Sheaf.pullback (ModuleCat.{0} k) f).obj F)
    hginv)).symm ≪≫ ((pullbackComp k e.inv g).app F).symm ≪≫
      (TopCat.Sheaf.pullback (ModuleCat.{0} k) e.inv).mapIso
        (((pullbackComp k (PerverseSheaves.openInclusion (TopCat.of U) V)
          U.inclusion').app F).symm ≪≫ i) ≪≫
          (constantPullback k e.inv).app A

/-- Kernels of morphisms of finite-rank local systems are finite-rank local systems. -/
public theorem localSystem_kernel (k : Type) [Field k] (Z : TopCat.{0})
    (F G : CoefficientSheaf k Z) (a : F ⟶ G)
    (hF : ConstructibleComplexes.IsFiniteRankLocalSystem k Z F)
    (hG : ConstructibleComplexes.IsFiniteRankLocalSystem k Z G) :
    ConstructibleComplexes.IsFiniteRankLocalSystem k Z (kernel a)
    := by
  intro x
  obtain ⟨UF, hxF, A, hA, ⟨iF⟩⟩ := hF x
  obtain ⟨UG, hxG, B, _, ⟨iG⟩⟩ := hG x
  let U := UF ⊓ UG
  let y : U := ⟨x, hxF, hxG⟩
  let T := TopCat.Sheaf.pullback (ModuleCat.{0} k) (PerverseSheaves.openInclusion Z U)
  let : PreservesFiniteLimits T :=
    pullback_preservesFiniteLimits k (PerverseSheaves.openInclusion Z U)
  let : T.Additive := pullback_additive k (PerverseSheaves.openInclusion Z U)
  let C := constantSheaf (Opens.grothendieckTopology (TopCat.of U)) (ModuleCat.{0} k)
  let eF : T.obj F ≅ C.obj A := refineModel k Z F UF U inf_le_left A iF
  let eG : T.obj G ≅ C.obj B := refineModel k Z G UG U inf_le_right B iG
  let b : C.obj A ⟶ C.obj B := eF.inv ≫ T.map a ≫ eG.hom
  let : FiniteDimensional k A := hA
  obtain ⟨V, hy, d, hd⟩ := constant_morphism_local k (TopCat.of U) A B b y
  let P := TopCat.Sheaf.pullback (ModuleCat.{0} k)
    (PerverseSheaves.openInclusion (TopCat.of U) V)
  let : PreservesFiniteLimits P :=
    pullback_preservesFiniteLimits k (PerverseSheaves.openInclusion (TopCat.of U) V)
  let R : CoefficientSheaf k (TopCat.of U) ⥤ CoefficientSheaf k (TopCat.of V) :=
    V.sheafRestrict
  let D := constantSheaf (Opens.grothendieckTopology (TopCat.of V)) (ModuleCat.{0} k)
  let eR : P ≅ R := V.isOpenEmbedding.sheafPullbackIso (ModuleCat.{0} k)
  let : PreservesFiniteLimits R := preservesFiniteLimits_of_natIso eR
  let : R.Additive := Functor.additive_of_preserves_binary_products R
  let : PreservesFiniteLimits D := by dsimp [D, constantSheaf]; infer_instance
  let eK : T.obj (kernel a) ≅ kernel b :=
    PreservesKernel.iso T a ≪≫ kernel.mapIso (T.map a) b eF eG (by simp [b])
  let eL : P.obj (kernel b) ≅ D.obj (kernel d) :=
    eR.app (kernel b) ≪≫ PreservesKernel.iso R b ≪≫
      (kernel.mapIso (D.map d) (R.map b) (restrictionConstantIso k (TopCat.of U) V A)
        (restrictionConstantIso k (TopCat.of U) V B) hd).symm ≪≫
          (PreservesKernel.iso D d).symm
  obtain ⟨W, hxW, iW⟩ := nestedModel k Z (kernel a) U y V hy (kernel d)
    (P.mapIso eK ≪≫ eL)
  refine ⟨W, hxW, kernel d, ?_, iW⟩
  exact FiniteDimensional.of_injective (ModuleCat.kernelIsoKer d).hom.hom
    (ModuleCat.kernelIsoKer d).toLinearEquiv.injective

end WantedExt.AlgebraicGeometry.ConstructibleComplexesWanted
