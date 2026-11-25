/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.Topology.Category.PointedCGWH.Closed

/-!
# Tests for the closed smash structure on pointed CGWH spaces
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory Limits MonoidalCategory Topology

namespace MathlibExtTest.PointedCGWHClosedTests

private theorem hasPullbacks : HasPullbacks CGWH.{u, v} := by
  let _ : HasLimitsOfSize.{v, v} CompactlyGenerated.{u, v} :=
    CategoryTheory.hasLimits_of_coreflective
      CompactlyGenerated.compactlyGeneratedToTop
  let _ : HasLimitsOfSize.{v, v} CGWH.{u, v} :=
    CategoryTheory.hasLimits_of_reflective
      CGWH.cgwhToCompactlyGenerated
  infer_instance

private noncomputable def unitToPointIso :
    𝟙_ CGWH.{u, v} ≅ CGWH.point.{u, v} :=
  CartesianMonoidalCategory.isTerminalTensorUnit.uniqueUpToIso
    CGWH.point_isTerminal

private noncomputable def baseInsertProbe
    (X : PointedCGWH.{u, v}) (A : CGWH.{u, v}) :
    A ⟶ X.right ⊗ A :=
  (λ_ A).inv ≫ (unitToPointIso.{u, v}).hom ▷ A ≫ X.hom ▷ A

private noncomputable def evBaseProbe
    (X Y : PointedCGWH.{u, v}) :
    (ihom X.right).obj Y.right ⟶ Y.right :=
  baseInsertProbe X ((ihom X.right).obj Y.right) ≫
    (ihom.ev X.right).app Y.right

private noncomputable def constBaseProbe
    (X Y : PointedCGWH.{u, v}) :
    CGWH.point.{u, v} ⟶ (ihom X.right).obj Y.right :=
  MonoidalClosed.curry
    (CartesianMonoidalCategory.snd X.right CGWH.point ≫ Y.hom)

@[reassoc]
private theorem baseInsert_fst_probe
    (X : PointedCGWH.{u, v}) (A : CGWH.{u, v}) :
    baseInsertProbe X A ≫ CartesianMonoidalCategory.fst X.right A =
      CGWH.point_isTerminal.from A ≫ X.hom := by
  dsimp only [baseInsertProbe]
  slice_lhs 3 4 =>
    rw [CartesianMonoidalCategory.whiskerRight_fst]
  slice_lhs 2 3 =>
    rw [CartesianMonoidalCategory.whiskerRight_fst]
  slice_lhs 1 2 =>
    rw [CartesianMonoidalCategory.leftUnitor_inv_fst]
  slice_lhs 1 2 =>
    rw [CGWH.point_isTerminal.hom_ext
      (CartesianMonoidalCategory.toUnit A ≫ unitToPointIso.hom)
      (CGWH.point_isTerminal.from A)]

@[reassoc]
private theorem baseInsert_snd_probe
    (X : PointedCGWH.{u, v}) (A : CGWH.{u, v}) :
    baseInsertProbe X A ≫ CartesianMonoidalCategory.snd X.right A =
      𝟙 A := by
  simp [baseInsertProbe, Category.assoc]

@[reassoc]
private theorem baseInsert_natural_probe
    (X : PointedCGWH.{u, v}) {A B : CGWH.{u, v}} (f : A ⟶ B) :
    f ≫ baseInsertProbe X B =
      baseInsertProbe X A ≫ X.right ◁ f := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, baseInsert_fst_probe,
      CartesianMonoidalCategory.whiskerLeft_fst]
    rw [← Category.assoc,
      CGWH.point_isTerminal.hom_ext
        (f ≫ CGWH.point_isTerminal.from B)
        (CGWH.point_isTerminal.from A)]
  · simp only [Category.assoc, baseInsert_snd_probe,
      CartesianMonoidalCategory.whiskerLeft_snd,
      Category.comp_id]
    rw [← Category.assoc, baseInsert_snd_probe, Category.id_comp]

private theorem constBase_evBase_probe
    (X Y : PointedCGWH.{u, v}) :
    constBaseProbe X Y ≫ evBaseProbe X Y = Y.hom := by
  dsimp only [evBaseProbe]
  slice_lhs 1 2 => rw [baseInsert_natural_probe]
  slice_lhs 2 3 => rw [← MonoidalClosed.uncurry_eq]
  rw [constBaseProbe, MonoidalClosed.uncurry_curry]
  slice_lhs 1 2 => rw [baseInsert_snd_probe]
  simp

private noncomputable def basedFstProbe
    (X Y : PointedCGWH.{u, v}) :
    ((PointedCGWH.basedInternalHom X).obj Y).right ⟶
      (ihom X.right).obj Y.right := by
  let _ : HasPullbacks CGWH.{u, v} := hasPullbacks
  exact eqToHom (show ((PointedCGWH.basedInternalHom X).obj Y).right =
        pullback (evBaseProbe X Y) Y.hom from rfl) ≫
      pullback.fst (evBaseProbe X Y) Y.hom

private noncomputable def basedSndProbe
    (X Y : PointedCGWH.{u, v}) :
    ((PointedCGWH.basedInternalHom X).obj Y).right ⟶ CGWH.point := by
  let _ : HasPullbacks CGWH.{u, v} := hasPullbacks
  exact eqToHom (show ((PointedCGWH.basedInternalHom X).obj Y).right =
        pullback (evBaseProbe X Y) Y.hom from rfl) ≫
      pullback.snd (evBaseProbe X Y) Y.hom

section PublicSurface

#check PointedCGWH.basedInternalHom
#check PointedCGWH.smashBasedHomAdjunction
#check PointedCGWH.basedEval
#check PointedCGWH.power
#check PointedCGWH.copower
#check PointedCGWH.enrichedHom
#check PointedCGWH.instMonoidalClosed

#check @PointedCGWH.basedInternalHom.{u, v}
#check @PointedCGWH.basedInternalHom.{0, 0}
#check @PointedCGWH.basedInternalHom.{1, 1}
#check @PointedCGWH.basedInternalHom.{0, 1}
#check @PointedCGWH.basedInternalHom.{1, 0}

#check @PointedCGWH.smashBasedHomAdjunction.{u, v}
#check @PointedCGWH.smashBasedHomAdjunction.{0, 0}
#check @PointedCGWH.smashBasedHomAdjunction.{1, 1}
#check @PointedCGWH.smashBasedHomAdjunction.{0, 1}
#check @PointedCGWH.smashBasedHomAdjunction.{1, 0}

#check @PointedCGWH.basedEval.{u, v}
#check @PointedCGWH.basedEval.{0, 0}
#check @PointedCGWH.basedEval.{1, 1}
#check @PointedCGWH.basedEval.{0, 1}
#check @PointedCGWH.basedEval.{1, 0}

#check @PointedCGWH.power.{u, v}
#check @PointedCGWH.power.{0, 0}
#check @PointedCGWH.power.{1, 1}
#check @PointedCGWH.power.{0, 1}
#check @PointedCGWH.power.{1, 0}

#check @PointedCGWH.copower.{u, v}
#check @PointedCGWH.copower.{0, 0}
#check @PointedCGWH.copower.{1, 1}
#check @PointedCGWH.copower.{0, 1}
#check @PointedCGWH.copower.{1, 0}

#check @PointedCGWH.enrichedHom.{u, v}
#check @PointedCGWH.enrichedHom.{0, 0}
#check @PointedCGWH.enrichedHom.{1, 1}
#check @PointedCGWH.enrichedHom.{0, 1}
#check @PointedCGWH.enrichedHom.{1, 0}

#synth MonoidalCategory PointedCGWH.{0, 0}
#synth MonoidalCategory PointedCGWH.{1, 1}
#synth MonoidalCategory PointedCGWH.{0, 1}
#synth MonoidalCategory PointedCGWH.{1, 0}
#synth SymmetricCategory PointedCGWH.{0, 0}
#synth SymmetricCategory PointedCGWH.{1, 1}
#synth SymmetricCategory PointedCGWH.{0, 1}
#synth SymmetricCategory PointedCGWH.{1, 0}
#synth MonoidalClosed PointedCGWH.{0, 0}
#synth MonoidalClosed PointedCGWH.{1, 1}
#synth MonoidalClosed PointedCGWH.{0, 1}
#synth MonoidalClosed PointedCGWH.{1, 0}

end PublicSurface

section PullbackCarrier

variable (X Y : PointedCGWH.{u, v})

local instance : HasPullbacks CGWH.{u, v} := hasPullbacks
local instance : BraidedCategory CGWH.{u, v} :=
  BraidedCategory.ofCartesianMonoidalCategory
local instance : SymmetricCategory CGWH.{u, v} := inferInstance

example : ((PointedCGWH.basedInternalHom X).obj Y).right =
    pullback (evBaseProbe X Y) Y.hom := rfl

example : (ihom X.right).obj Y.right =
    CGWH.internalHom X.right Y.right :=
  CGWH.ihom_obj_eq_internalHom X.right Y.right

example : baseInsertProbe X ((ihom X.right).obj Y.right) ≫
      CartesianMonoidalCategory.fst X.right ((ihom X.right).obj Y.right) =
    CGWH.point_isTerminal.from ((ihom X.right).obj Y.right) ≫ X.hom := by
  exact baseInsert_fst_probe X _

example : baseInsertProbe X ((ihom X.right).obj Y.right) ≫
      CartesianMonoidalCategory.snd X.right ((ihom X.right).obj Y.right) =
    𝟙 ((ihom X.right).obj Y.right) := by
  exact baseInsert_snd_probe X _

example : constBaseProbe X Y ≫ evBaseProbe X Y = Y.hom :=
  constBase_evBase_probe X Y

example : ((PointedCGWH.basedInternalHom X).obj Y).hom ≫
      pullback.fst (evBaseProbe X Y) Y.hom =
    constBaseProbe X Y := by
  change pullback.lift (constBaseProbe X Y) (𝟙 CGWH.point) _ ≫
      pullback.fst (evBaseProbe X Y) Y.hom = _
  generalize_proofs _ hGeneric
  have hProbe : constBaseProbe X Y ≫ evBaseProbe X Y =
      (𝟙 CGWH.point) ≫ Y.hom := by
    simpa only [Category.id_comp] using constBase_evBase_probe X Y
  have hTransport : hGeneric = hProbe := Subsingleton.elim _ _
  rw [hTransport, pullback.lift_fst]

example : ((PointedCGWH.basedInternalHom X).obj Y).hom ≫
      pullback.snd (evBaseProbe X Y) Y.hom =
    𝟙 CGWH.point := by
  change pullback.lift (constBaseProbe X Y) (𝟙 CGWH.point) _ ≫
      pullback.snd (evBaseProbe X Y) Y.hom = _
  generalize_proofs _ hGeneric
  have hProbe : constBaseProbe X Y ≫ evBaseProbe X Y =
      (𝟙 CGWH.point) ≫ Y.hom := by
    simpa only [Category.id_comp] using constBase_evBase_probe X Y
  have hTransport : hGeneric = hProbe := Subsingleton.elim _ _
  rw [hTransport, pullback.lift_snd]

example {Y' : PointedCGWH.{u, v}} (g : Y ⟶ Y') :
    ((PointedCGWH.basedInternalHom X).map g).right ≫
        basedFstProbe X Y' =
      basedFstProbe X Y ≫
        (ihom X.right).map g.right := by
  unfold PointedCGWH.basedInternalHom
  unfold CategoryTheory.Pointed.basedInternalHom
  unfold basedFstProbe
  simp only [Under.homMk_right]
  dsimp only [pullback.map]
  exact pullback.lift_fst _ _ _

example {Y' : PointedCGWH.{u, v}} (g : Y ⟶ Y') :
    ((PointedCGWH.basedInternalHom X).map g).right ≫
        basedSndProbe X Y' = basedSndProbe X Y := by
  exact CGWH.point_isTerminal.hom_ext _ _

example : IsClosed
    ((ConcreteCategory.hom (evBaseProbe X Y)) ⁻¹'
      {Y.hom (show CGWH.point.{u, v} from PUnit.unit)}) :=
  isClosed_singleton.preimage
    (ConcreteCategory.hom (evBaseProbe X Y)).continuous

example : IsClosedEmbedding
    (ConcreteCategory.hom (basedFstProbe X Y)) := by
  let H : CGWH.{u, v} := (ihom X.right).obj Y.right
  let y₀ : Y.right := Y.hom
    (show CGWH.point.{u, v} from PUnit.unit)
  let S : Set H := (ConcreteCategory.hom (evBaseProbe X Y)) ⁻¹' {y₀}
  have hS : IsClosed S := isClosed_singleton.preimage
    (ConcreteCategory.hom (evBaseProbe X Y)).continuous
  let _ : ∀ (K : CompHaus.{u}) (F : TopologicalSpace.Closeds K),
      IsGeneratedBy CompactlyGenerated.compactHausProbes.{u} F :=
    fun _ F => by
      let _ : CompactSpace F :=
        isCompact_iff_compactSpace.mp F.isClosed.isCompact
      exact Topology.isGeneratedBy_compactHausProbes_iff.mpr inferInstance
  let _ : IsGeneratedBy CompactlyGenerated.compactHausProbes.{u} H :=
    Topology.isGeneratedBy_compactHausProbes_iff.mpr inferInstance
  let _ : IsGeneratedBy CompactlyGenerated.compactHausProbes.{u} S :=
    hS.isGeneratedBy
  let _ : UCompactlyGeneratedSpace.{u} S :=
    Topology.isGeneratedBy_compactHausProbes_iff.mp inferInstance
  let _ : UWeakHausdorffSpace.{u} S :=
    { isClosed_range := fun K f => by
        let f' : C(K, H) :=
          ⟨fun k => (f k).1, continuous_subtype_val.comp f.continuous⟩
        have hf' : IsClosed (Set.range f') :=
          UWeakHausdorffSpace.isClosed_range K f'
        rw [show Set.range f =
            Subtype.val ⁻¹' Set.range f' by
          ext z
          constructor
          · rintro ⟨k, rfl⟩
            exact ⟨k, rfl⟩
          · rintro ⟨k, hk⟩
            exact ⟨k, Subtype.ext hk⟩]
        exact hf'.preimage continuous_subtype_val }
  let Q : CGWH.{u, v} := CGWH.of S
  let i : Q ⟶ H := ConcreteCategory.ofHom
    ⟨Subtype.val, continuous_subtype_val⟩
  let r : Q ⟶ CGWH.point.{u, v} :=
    CGWH.point_isTerminal.from Q
  have point_ext (a b : CGWH.point.{u, v}) : a = b := by
    change PUnit.{v + 1} at a b
    exact Subsingleton.elim a b
  have hcomm : i ≫ evBaseProbe X Y = r ≫ Y.hom := by
    apply ConcreteCategory.hom_ext
    intro z
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    have hi : i z = z.1 := rfl
    rw [hi]
    have hz : evBaseProbe X Y z.1 = y₀ := by
      exact (Set.mem_singleton_iff.mp z.2)
    exact hz.trans (congrArg (fun p => Y.hom p)
      (point_ext (show CGWH.point.{u, v} from PUnit.unit) (r z)))
  let c : PullbackCone (evBaseProbe X Y) Y.hom :=
    PullbackCone.mk i r hcomm
  have hc : IsLimit c := by
    apply PullbackCone.IsLimit.mk hcomm
    case lift =>
      intro s
      apply ConcreteCategory.ofHom
      refine ⟨(fun z => ⟨s.fst z, ?_⟩), ?_⟩
      · change evBaseProbe X Y (s.fst z) = y₀
        have hz := ConcreteCategory.congr_hom s.condition z
        change evBaseProbe X Y (s.fst z) = Y.hom (s.snd z) at hz
        exact hz.trans (congrArg (fun p => Y.hom p)
          (point_ext (s.snd z)
            (show CGWH.point.{u, v} from PUnit.unit)))
      · fun_prop
    case fac_left =>
      intro s
      apply ConcreteCategory.hom_ext
      intro z
      rfl
    case fac_right =>
      intro s
      exact CGWH.point_isTerminal.hom_ext _ _
    case uniq =>
      intro s m hm _
      apply ConcreteCategory.hom_ext
      intro z
      apply Subtype.ext
      exact ConcreteCategory.congr_hom hm z
  let hQ : IsPullback i r (evBaseProbe X Y) Y.hom :=
    IsPullback.of_isLimit hc
  let hPB := IsPullback.of_hasPullback (evBaseProbe X Y) Y.hom
  let e : Q ≅ pullback (evBaseProbe X Y) Y.hom :=
    hQ.isoIsPullback _ _ hPB
  have he : e.inv ≫ i = pullback.fst (evBaseProbe X Y) Y.hom := by
    exact hQ.isoIsPullback_inv_fst _ _ hPB
  have hi : IsClosedEmbedding (ConcreteCategory.hom i) := by
    simpa [i, Q] using hS.isClosedEmbedding_subtypeVal
  have hcomp := hi.comp (CGWH.homeoOfIso e.symm).isClosedEmbedding
  change IsClosedEmbedding (ConcreteCategory.hom (e.inv ≫ i)) at hcomp
  rw [he] at hcomp
  let t : ((PointedCGWH.basedInternalHom X).obj Y).right ⟶
      pullback (evBaseProbe X Y) Y.hom :=
    eqToHom (show ((PointedCGWH.basedInternalHom X).obj Y).right =
      pullback (evBaseProbe X Y) Y.hom from rfl)
  have ht : IsClosedEmbedding (ConcreteCategory.hom t) :=
    (CGWH.homeoOfIso (asIso t)).isClosedEmbedding
  have hfinal := hcomp.comp ht
  change IsClosedEmbedding (ConcreteCategory.hom
    (t ≫ pullback.fst (evBaseProbe X Y) Y.hom)) at hfinal
  exact hfinal

end PullbackCarrier

section FactoryIdentity

variable (X : PointedCGWH.{u, v})

local instance : HasPullbacks CGWH.{u, v} := hasPullbacks
local instance : BraidedCategory CGWH.{u, v} :=
  BraidedCategory.ofCartesianMonoidalCategory
local instance : SymmetricCategory CGWH.{u, v} := inferInstance

example : PointedCGWH.basedInternalHom X =
    CategoryTheory.Pointed.basedInternalHom
      CGWH.point CGWH.point_isTerminal X := rfl

example : PointedCGWH.smashBasedHomAdjunction X =
    CategoryTheory.Pointed.smashBasedHomAdjunction
      CGWH.point CGWH.point_isTerminal X := rfl

example : PointedCGWH.basedEval X =
    CategoryTheory.Pointed.basedEval
      CGWH.point CGWH.point_isTerminal X := rfl

example : PointedCGWH.power X =
    CategoryTheory.Pointed.power
      CGWH.point CGWH.point_isTerminal X := rfl

example : PointedCGWH.copower X =
    CategoryTheory.Pointed.copower
      CGWH.point CGWH.point_isTerminal X := rfl

example : (inferInstance : MonoidalClosed PointedCGWH.{u, v}) =
    (CategoryTheory.Pointed.smashMonoidalClosed
      CGWH.point CGWH.point_isTerminal) := rfl

example : (inferInstance : MonoidalClosed PointedCGWH.{u, v}) =
    PointedCGWH.instMonoidalClosed := rfl

end FactoryIdentity

section Adjunction

variable (X Z Y : PointedCGWH.{u, v})

example (f : (PointedCGWH.smash.obj X).obj Z ⟶ Y) :
    Z ⟶ (PointedCGWH.basedInternalHom X).obj Y :=
  (PointedCGWH.smashBasedHomAdjunction X).homEquiv Z Y f

example (g : Z ⟶ (PointedCGWH.basedInternalHom X).obj Y) :
    (PointedCGWH.smash.obj X).obj Z ⟶ Y :=
  ((PointedCGWH.smashBasedHomAdjunction X).homEquiv Z Y).symm g

example (f : (PointedCGWH.smash.obj X).obj Z ⟶ Y) :
    ((PointedCGWH.smashBasedHomAdjunction X).homEquiv Z Y).symm
        ((PointedCGWH.smashBasedHomAdjunction X).homEquiv Z Y f) = f :=
  Equiv.symm_apply_apply _ f

example (g : Z ⟶ (PointedCGWH.basedInternalHom X).obj Y) :
    (PointedCGWH.smashBasedHomAdjunction X).homEquiv Z Y
        (((PointedCGWH.smashBasedHomAdjunction X).homEquiv Z Y).symm g) = g :=
  Equiv.apply_symm_apply _ g

example {Z' : PointedCGWH.{u, v}} (k : Z' ⟶ Z)
    (g : Z ⟶ (PointedCGWH.basedInternalHom X).obj Y) :
    ((PointedCGWH.smashBasedHomAdjunction X).homEquiv Z' Y).symm
        (k ≫ g) =
      (PointedCGWH.smash.obj X).map k ≫
        ((PointedCGWH.smashBasedHomAdjunction X).homEquiv Z Y).symm g :=
  (PointedCGWH.smashBasedHomAdjunction X).homEquiv_naturality_left_symm k g

example {Y' : PointedCGWH.{u, v}}
    (f : (PointedCGWH.smash.obj X).obj Z ⟶ Y) (g : Y ⟶ Y') :
    (PointedCGWH.smashBasedHomAdjunction X).homEquiv Z Y' (f ≫ g) =
      (PointedCGWH.smashBasedHomAdjunction X).homEquiv Z Y f ≫
        (PointedCGWH.basedInternalHom X).map g :=
  (PointedCGWH.smashBasedHomAdjunction X).homEquiv_naturality_right f g

example : PointedCGWH.basedEval X =
    (PointedCGWH.smashBasedHomAdjunction X).counit := rfl

example :
    (PointedCGWH.smash.obj X).map
          ((PointedCGWH.smashBasedHomAdjunction X).unit.app Z) ≫
        (PointedCGWH.basedEval X).app
          ((PointedCGWH.smash.obj X).obj Z) =
      𝟙 ((PointedCGWH.smash.obj X).obj Z) :=
  (PointedCGWH.smashBasedHomAdjunction X).left_triangle_components Z

example :
    (PointedCGWH.smashBasedHomAdjunction X).unit.app
          ((PointedCGWH.basedInternalHom X).obj Y) ≫
        (PointedCGWH.basedInternalHom X).map
          ((PointedCGWH.basedEval X).app Y) =
      𝟙 ((PointedCGWH.basedInternalHom X).obj Y) :=
  (PointedCGWH.smashBasedHomAdjunction X).right_triangle_components Y

example : PointedCGWH.power X = PointedCGWH.basedInternalHom X := rfl

example : PointedCGWH.copower X = PointedCGWH.smash.obj X := rfl

end Adjunction

section ScopeOff

example : True := by
  fail_if_success
    let _ : EnrichedCategory PointedCGWH.{u, v} PointedCGWH.{u, v} :=
      inferInstance
  trivial

end ScopeOff

section ScopeOn

open scoped MonoidalClosed

#synth EnrichedCategory PointedCGWH.{u, v} PointedCGWH.{u, v}
#synth EnrichedOrdinaryCategory PointedCGWH.{u, v} PointedCGWH.{u, v}

variable (X Y : PointedCGWH.{u, v})

example : PointedCGWH.enrichedHom X Y =
    (PointedCGWH.basedInternalHom X).obj Y := rfl

example : EnrichedCategory.Hom X Y =
    PointedCGWH.enrichedHom X Y := rfl

example {Y' : PointedCGWH.{u, v}} (g : Y ⟶ Y') :
    eHomWhiskerLeft PointedCGWH.{u, v} X g =
      (PointedCGWH.basedInternalHom X).map g :=
  MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerLeft
    PointedCGWH.{u, v} X g

example {X' : PointedCGWH.{u, v}} (f : X ⟶ X') :
    eHomWhiskerRight PointedCGWH.{u, v} f Y =
      (MonoidalClosed.pre f).app Y :=
  MonoidalClosed.enrichedOrdinaryCategorySelf_eHomWhiskerRight
    PointedCGWH.{u, v} f Y

end ScopeOn

section ScopeTeardown

example : True := by
  fail_if_success
    let _ : EnrichedCategory PointedCGWH.{u, v} PointedCGWH.{u, v} :=
      inferInstance
  trivial

end ScopeTeardown

section InstanceDeletion

attribute [-instance] PointedCGWH.instMonoidalClosed in
example : True := by
  fail_if_success
    let _ : MonoidalClosed PointedCGWH.{u, v} := inferInstance
  trivial

end InstanceDeletion

section PrivacyAndNonclaims

#guard_msgs (error, substring := true) in
#check PointedCGWH.hasPullbacks

#guard_msgs (error, substring := true) in
#check PointedCGWH.basedInternalHomPullback

#guard_msgs (error, substring := true) in
#check PointedCGWH.instEnrichedCategory

#guard_msgs (error, substring := true) in
#check PointedCGWH.rawBasedInternalHom

#guard_msgs (error, substring := true) in
#check PointedCGWH.internalHomToCompactOpen

#guard_msgs (error, substring := true) in
#check PointedCGWH.smashModelCategory

#guard_msgs (error, substring := true) in
#check PointedCGWH.adj_isQuillenEquivalence

#guard_msgs (error, substring := true) in
#check PointedCGWH.pushoutProduct

#guard_msgs (error, substring := true) in
#check PointedCGWH.monoidAxiom

#guard_msgs (error, substring := true) in
#check PointedCGWH.sphereOne

#guard_msgs (error, substring := true) in
#check PointedCGWH.spectrum

end PrivacyAndNonclaims

#print axioms PointedCGWH.basedInternalHom
#print axioms PointedCGWH.smashBasedHomAdjunction
#print axioms PointedCGWH.basedEval
#print axioms PointedCGWH.power
#print axioms PointedCGWH.copower
#print axioms PointedCGWH.enrichedHom
#print axioms PointedCGWH.instMonoidalClosed

end MathlibExtTest.PointedCGWHClosedTests
