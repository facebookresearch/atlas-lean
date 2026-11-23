/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.CWTypeMapping
public import MathlibExt.Topology.CWComplex.SingularModel
public import MathlibExt.Topology.Category.TopCat.TrivialCofibrationExtension
public import MathlibExt.Topology.Homotopy.PointRelativeComposition

/-!
# Source-point-relative mapping for actual CW-type plus maps

Actual point cofibrations give a based inverse of the original singular
counit. The constructed plus of that singular realization is compared to
the chosen target by the original strict classical comparison, with a based
inverse derived in the existing Under model category. Transporting the
constructed extension and its relative uniqueness then retains the original
source point. No arbitrary plus map is assumed to be a cofibration.

The point cofibrations are structural additional hypotheses for this based
companion. They are derived for the actual realized and cell-constructed
spaces in the Q/plus application; the general unbased theorem is unchanged.
-/

noncomputable section

open CategoryTheory HomotopicalAlgebra
open AlgebraicTopology AlgebraicTopology.LoopCellIndependentPlus
open scoped ContinuousMap Simplicial TopCat.modelCategory

universe u v w z vB

namespace TopCat.IsPlusConstructionAt

private def precomposePointRelative
    {C X H : TopCat.{u}} {f g : C ⟶ H} (c : C) (x : X)
    (K : ContinuousMap.HomotopyRel f.hom g.hom {c})
    (r : X ⟶ C) (hr : r x = c) :
    ContinuousMap.HomotopyRel (r ≫ f).hom (r ≫ g).hom {x} :=
  (K.precomposePointRelative r.hom x hr).cast
    (TopCat.hom_comp r f).symm (TopCat.hom_comp r g).symm

private def restrictPoint
    {A H : TopCat.{u}} {f g : A ⟶ H} {S : Set A} (a : A)
    (K : ContinuousMap.HomotopyRel f.hom g.hom S) (ha : a ∈ S) :
    ContinuousMap.HomotopyRel f.hom g.hom {a} :=
  { toHomotopy := K.toHomotopy
    prop' := by
      intro t y hy
      have hya : y = a := Set.mem_singleton_iff.mp hy
      subst y
      exact K.eq_fst t ha }

private def descendPointRelative
    {C X H : TopCat.{u}} (s : C ⟶ X) (r : X ⟶ C)
    (x : X) (c : C) (hr : r x = c)
    (R : ContinuousMap.HomotopyRel (r ≫ s).hom (𝟙 X : X ⟶ X).hom {x})
    (f g : X ⟶ H)
    (K : ContinuousMap.HomotopyRel (s ≫ f).hom (s ≫ g).hom {c}) :
    ContinuousMap.HomotopyRel f.hom g.hom {x} := by
  let P : ContinuousMap.HomotopyRel ((r ≫ s) ≫ f).hom ((r ≫ s) ≫ g).hom {x} :=
    (precomposePointRelative c x K r hr).cast
      (congrArg TopCat.Hom.hom (Category.assoc r s f).symm)
      (congrArg TopCat.Hom.hom (Category.assoc r s g).symm)
  let RF : ContinuousMap.HomotopyRel ((r ≫ s) ≫ f).hom f.hom {x} :=
    (R.compContinuousMap f.hom).cast
      (TopCat.hom_comp (r ≫ s) f).symm
      ((TopCat.hom_comp (𝟙 X) f).symm.trans
        (congrArg TopCat.Hom.hom (Category.id_comp f)))
  let RG : ContinuousMap.HomotopyRel ((r ≫ s) ≫ g).hom g.hom {x} :=
    (R.compContinuousMap g.hom).cast
      (TopCat.hom_comp (r ≫ s) g).symm
      ((TopCat.hom_comp (𝟙 X) g).symm.trans
        (congrArg TopCat.Hom.hom (Category.id_comp g)))
  exact RF.symm.trans (P.trans RG)

/-- Actual CW-type plus data and structural source/target point
cofibrations derive a literal based factor, an original source-point-relative
triangle, and point-relative uniqueness in both directions. Neither a
cofibration on the arbitrary plus map nor comparison/model/inverse/extended
homotopy data is supplied. The target of the original map may have arbitrary
components, and the original map must kill the prescribed subgroup at its
actual image point. -/
public theorem exists_point_relative_extension_of_cwType
    {X A : TopCat.{u}} [ConnectedSpace A]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
    (hCWA : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ A))
    {i : X ⟶ A} {x : X} {a : A} {hix : i x = a}
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A)]
    {P : Subgroup (FundamentalGroup X x)} [P.Normal] [Group.IsPerfect P]
    (hi : TopCat.IsPlusConstructionAt i x a hix P)
    (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) :
    ∃ F : A ⟶ H, F a = f x ∧
      Nonempty (ContinuousMap.HomotopyRel (i ≫ F).hom f.hom {x}) ∧
      ∀ G₀ : A ⟶ H, Nonempty (ContinuousMap.HomotopyRel (i ≫ G₀).hom f.hom {x}) →
        Nonempty (ContinuousMap.HomotopyRel F.hom G₀.hom {a}) ∧
        Nonempty (ContinuousMap.HomotopyRel G₀.hom F.hom {a}) := by
  obtain ⟨CA, hTA, hCA, ⟨eA⟩⟩ := hCWA
  letI : T2Space CA := hTA
  letI : Topology.CWComplex (Set.univ : Set CA) := hCA
  letI : PathConnectedSpace A :=
    Topology.CWComplex.pathConnectedSpace_of_connected_CWType eA
  letI : PathConnectedSpace X := by
    let F : TopCat.{u} := TopCat.homotopyFiber i a
    let p : F ⟶ X := TopCat.homotopyFiberToTotal i a
    let z₀ : F := TopCat.loopToHomotopyFiber i x a hix (Path.refl a)
    letI : PathConnectedSpace F :=
      TopCat.pathConnectedSpace_of_isZero_reducedIntegralH0 F z₀ (hi.acyclic 0)
    have hp : Function.Surjective p := by
      intro z
      let q : Path (i z) a := PathConnectedSpace.somePath (i z) a
      let t := TopCat.loopToHomotopyFiber i z (i z) rfl (Path.refl (i z))
      refine ⟨TopCat.homotopyFiberBasepointChange i q t, ?_⟩
      exact (ConcreteCategory.congr_hom
        (TopCat.homotopyFiberBasepointChange_toTotal i q) t).trans
        (ConcreteCategory.congr_hom
          (TopCat.loopToHomotopyFiber_toTotal i z (i z) rfl) (Path.refl (i z)))
    exact hp.pathConnectedSpace p.hom.continuous
  let C := SSet.toTop.obj (TopCat.toSSet.obj X)
  let c : C := SSet.realizedVertex (TopCat.toSSetObj₀Equiv.symm x)
  let s := sSetTopAdj.counit.app X
  have hs : s c = x :=
    (TopCat.counit_realizedVertex (TopCat.toSSetObj₀Equiv.symm x)).trans
      (TopCat.toSSetObj₀Equiv.apply_symm_apply x)
  obtain ⟨r, hr, _, ⟨RX⟩⟩ := TopCat.singularRealization_based_inverse_of_cofibrant_point X x
  let m := FundamentalGroup.mapOfEq s.hom hs
  let Q := P.comap m
  letI : T2Space C := SSet.realization_t2Space (TopCat.toSSet.obj X)
  letI : Topology.CWComplex (Set.univ : Set C) := inferInstance
  letI : PathConnectedSpace C :=
    TopCat.singularRealization_pathConnected_of_connected_CWType X hCWX
  obtain ⟨hN, hQ, hiC, _⟩ := hi.on_singularRealization
  letI : Q.Normal := hN
  letI : Group.IsPerfect Q := hQ
  let B := LoopCellRegularThreeComparison.originalThree C c Q
  let iC : C ⟶ B := LoopCellAttachment.inclusion C c Q ≫
    LoopCellRegularThreeComparison.originalThreeInclusion C c Q
  let b := LoopCellRegularThreeComparison.originalThreeBasePoint C c Q
  have hib : iC c = b := rfl
  letI : Cofibration iC := originalInclusion_cofibration C c Q
  letI : Cofibration (TopCat.const c : TopCat.of PUnit.{u + 1} ⟶ C) :=
    SSet.realizedVertex_pointMap_cofibration (TopCat.toSSet.obj X)
      (TopCat.toSSetObj₀Equiv.symm x)
  letI : Cofibration (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B) := by
    have he : (TopCat.const c : TopCat.of PUnit.{u + 1} ⟶ C) ≫ iC =
        (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B) := by
      apply TopCat.hom_ext
      apply ContinuousMap.ext
      intro p
      exact hib
    rw [← he]
    infer_instance
  obtain ⟨T, hT, eT, heT, _⟩ :=
    original_connected_CW_plus_comparison C c Q A ⟨CA, hTA, hCA, ⟨eA⟩⟩
      (s ≫ i) a ((congrArg i hs).trans hix) hiC
  have hTb : T b = a :=
    (congrArg T hib.symm).trans
      ((ConcreteCategory.congr_hom hT c).trans ((congrArg i hs).trans hix))
  have heT' : TopCat.ofHom eT.toFun = T := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro y
    exact congrArg (fun k => k y) heT
  have hTW : TopCat.weakHomotopyEquivalences T := by
    have h := TopCat.homotopyEquiv_toFun_mem eT
    rw [heT'] at h
    exact h
  obtain ⟨G, hGab, ⟨KTG⟩, ⟨KGT⟩⟩ :=
    TopCat.exists_based_inverse_of_weak_of_cofibrant_points B A b a T hTb hTW
  let cf := s ≫ f
  have hcf : cf c = f x := congrArg f hs
  have hmap : FundamentalGroup.mapOfEq (s ≫ f).hom hcf =
      (FundamentalGroup.mapOfEq f.hom rfl).comp m := by
    have hcomp : (f.hom.comp s.hom) c = f x :=
      congrArg (fun z : X => f.hom z) hs
    have hMap := FundamentalGroup.mapOfEq_comp (x := c) (y := x) (z := f x)
      s.hom f.hom hs rfl hcomp
    simpa only [TopCat.hom_comp, m] using hMap
  have hkillC : ∀ q ∈ Q, FundamentalGroup.mapOfEq cf.hom rfl q = 1 := by
    intro q hq
    apply (FundamentalGroup.mapOfEq_eq_one_iff cf.hom hcf q).mp
    exact (congrArg (fun k => k q) hmap).trans (hkill (m q) hq)
  obtain ⟨_, Fc, _, hFc, _, _, _, _, hUnique⟩ :=
    original_connected_CW_plus_map_extension C c Q H cf hkillC
  let F := G ≫ Fc
  let KTF : ContinuousMap.HomotopyRel (T ≫ F).hom Fc.hom {b} :=
    (KTG.compContinuousMap Fc.hom).cast
      ((TopCat.hom_comp (T ≫ G) Fc).symm.trans
        (congrArg TopCat.Hom.hom (Category.assoc T G Fc)))
      ((TopCat.hom_comp (𝟙 B) Fc).symm.trans
        (congrArg TopCat.Hom.hom (Category.id_comp Fc)))
  have hstart : iC ≫ (T ≫ F) = s ≫ (i ≫ F) :=
    (Category.assoc iC T F).symm.trans
      ((congrArg (fun k => k ≫ F) hT).trans (Category.assoc s i F))
  let KC : ContinuousMap.HomotopyRel (s ≫ (i ≫ F)).hom (s ≫ f).hom {c} :=
    (precomposePointRelative b c KTF iC hib).cast
      (congrArg TopCat.Hom.hom hstart) (congrArg TopCat.Hom.hom hFc)
  let K := descendPointRelative s r x c hr RX (i ≫ F) f KC
  have hFpoint : F a = f x :=
    (congrArg F hix.symm).trans
      ((K.eq_fst 1 (Set.mem_singleton x)).symm.trans (K.map_one_left x))
  refine ⟨F, hFpoint, ⟨K⟩, ?_⟩
  intro G₀ hG₀
  have hstart₀ : iC ≫ (T ≫ G₀) = s ≫ (i ≫ G₀) :=
    (Category.assoc iC T G₀).symm.trans
      ((congrArg (fun k => k ≫ G₀) hT).trans (Category.assoc s i G₀))
  let KR : ContinuousMap.HomotopyRel (iC ≫ (T ≫ G₀)).hom cf.hom {c} :=
    (precomposePointRelative x c hG₀.some s hs).cast
      (congrArg TopCat.Hom.hom hstart₀.symm) rfl
  obtain ⟨R, LR, hR, _⟩ :=
    TopCat.exists_homotopyExtensionRel_of_cofibration iC {c} (T ≫ G₀) cf KR
  let LRP := restrictPoint b LR (show b ∈ iC '' ({c} : Set C) from
    ⟨c, Set.mem_singleton c, hib⟩)
  let HU := restrictPoint b (hUnique R hR).1.some
    (show b ∈ Set.range iC from ⟨c, hib⟩)
  let KT : ContinuousMap.HomotopyRel (T ≫ F).hom (T ≫ G₀).hom {b} :=
    KTF.trans (HU.trans LRP.symm)
  let KM := descendPointRelative T G a b hGab KGT F G₀ KT
  exact ⟨⟨KM⟩, ⟨KM.symm⟩⟩

/-- Two actual CW-type plus maps killing the same subgroup have a derived
based target equivalence, BOTH singleton-relative inverse families and BOTH
source-point-relative comparison triangles. The actual point cofibrations
are structural inputs to this based companion; the arbitrary plus maps need
not be cofibrations, and no comparison or inverse homotopies are supplied. -/
public theorem point_relative_homotopyEquiv_of_same_subgroup_cwType
    {X A B : TopCat.{u}} [ConnectedSpace A] [ConnectedSpace B]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
    (hCWA : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ A))
    (hCWB : ∃ C : TopCat.{z}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ B))
    {i : X ⟶ A} {j : X ⟶ B} {x : X} {a : A} {b : B}
    {hix : i x = a} {hjx : j x = b}
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A)]
    [Cofibration (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B)]
    {P : Subgroup (FundamentalGroup X x)} [P.Normal] [Group.IsPerfect P]
    (hi : TopCat.IsPlusConstructionAt i x a hix P)
    (hj : TopCat.IsPlusConstructionAt j x b hjx P) :
    ∃ F : A ⟶ B, ∃ G : B ⟶ A, ∃ e : A ≃ₕ B,
      e.toFun = F.hom ∧ e.invFun = G.hom ∧ F a = b ∧ G b = a ∧
        Nonempty (ContinuousMap.HomotopyRel (F ≫ G).hom (𝟙 A : A ⟶ A).hom {a}) ∧
        Nonempty (ContinuousMap.HomotopyRel (G ≫ F).hom (𝟙 B : B ⟶ B).hom {b}) ∧
        Nonempty (ContinuousMap.HomotopyRel (i ≫ F).hom j.hom {x}) ∧
        Nonempty (ContinuousMap.HomotopyRel (j ≫ G).hom i.hom {x}) := by
  have hkillI : ∀ p ∈ P, FundamentalGroup.mapOfEq i.hom rfl p = 1 := by
    intro p hp
    apply (FundamentalGroup.mapOfEq_eq_one_iff i.hom hix p).mp
    apply MonoidHom.mem_ker.mp
    rw [hi.kernel_eq]
    exact hp
  have hkillJ : ∀ p ∈ P, FundamentalGroup.mapOfEq j.hom rfl p = 1 := by
    intro p hp
    apply (FundamentalGroup.mapOfEq_eq_one_iff j.hom hjx p).mp
    apply MonoidHom.mem_ker.mp
    rw [hj.kernel_eq]
    exact hp
  obtain ⟨F, hFa, ⟨KF⟩, _⟩ :=
    hi.exists_point_relative_extension_of_cwType hCWX hCWA B j hkillJ
  obtain ⟨G, hGb, ⟨KG⟩, _⟩ :=
    hj.exists_point_relative_extension_of_cwType hCWX hCWB A i hkillI
  have hFab : F a = b := hFa.trans hjx
  have hGba : G b = a := hGb.trans hix
  let KFA : ContinuousMap.HomotopyRel (i ≫ (F ≫ G)).hom i.hom {x} :=
    (((KF.compContinuousMap G.hom).cast
      (TopCat.hom_comp (i ≫ F) G).symm (TopCat.hom_comp j G).symm).trans KG).cast
        (congrArg TopCat.Hom.hom (Category.assoc i F G)) rfl
  let KGB : ContinuousMap.HomotopyRel (j ≫ (G ≫ F)).hom j.hom {x} :=
    (((KG.compContinuousMap F.hom).cast
      (TopCat.hom_comp (j ≫ G) F).symm (TopCat.hom_comp i F).symm).trans KF).cast
        (congrArg TopCat.Hom.hom (Category.assoc j G F)) rfl
  let KIA : ContinuousMap.HomotopyRel (i ≫ 𝟙 A).hom i.hom {x} :=
    (ContinuousMap.HomotopyRel.refl i.hom {x}).cast
      (congrArg TopCat.Hom.hom (Category.comp_id i).symm) rfl
  let KIB : ContinuousMap.HomotopyRel (j ≫ 𝟙 B).hom j.hom {x} :=
    (ContinuousMap.HomotopyRel.refl j.hom {x}).cast
      (congrArg TopCat.Hom.hom (Category.comp_id j).symm) rfl
  obtain ⟨_, _, _, uA⟩ :=
    hi.exists_point_relative_extension_of_cwType hCWX hCWA A i hkillI
  obtain ⟨_, _, _, uB⟩ :=
    hj.exists_point_relative_extension_of_cwType hCWX hCWB B j hkillJ
  let KA : ContinuousMap.HomotopyRel (F ≫ G).hom (𝟙 A : A ⟶ A).hom {a} :=
    (uA (F ≫ G) ⟨KFA⟩).1.some.symm.trans ((uA (𝟙 A) ⟨KIA⟩).1.some)
  let KB : ContinuousMap.HomotopyRel (G ≫ F).hom (𝟙 B : B ⟶ B).hom {b} :=
    (uB (G ≫ F) ⟨KGB⟩).1.some.symm.trans ((uB (𝟙 B) ⟨KIB⟩).1.some)
  let e : A ≃ₕ B :=
    { toFun := F.hom
      invFun := G.hom
      left_inv := ⟨KA.toHomotopy.cast (TopCat.hom_comp F G) (TopCat.hom_id (X := A))⟩
      right_inv := ⟨KB.toHomotopy.cast (TopCat.hom_comp G F) (TopCat.hom_id (X := B))⟩ }
  exact ⟨F, G, e, rfl, rfl, hFab, hGba, ⟨KA⟩, ⟨KB⟩, ⟨KF⟩, ⟨KG⟩⟩

/-- A subgroup-preserving original source map induces an actual based
map between chosen plus targets, together with its source-point-relative
triangle and both point-relative uniqueness families. The killing premise
is derived from the literal target-plus kernel and original pi1 composition.
The target plus map need not be a cofibration. -/
public theorem exists_point_relative_subgroup_preserving_extension_of_cwType
    {X A Y B : TopCat.{u}} [ConnectedSpace A]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
    (hCWA : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ A))
    {i : X ⟶ A} {j : Y ⟶ B} {x : X} {a : A} {y : Y} {b : B}
    {hix : i x = a} {hjy : j y = b}
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A)]
    {P : Subgroup (FundamentalGroup X x)} {Q : Subgroup (FundamentalGroup Y y)}
    [P.Normal] [Group.IsPerfect P] [Q.Normal] [Group.IsPerfect Q]
    (hi : TopCat.IsPlusConstructionAt i x a hix P)
    (hj : TopCat.IsPlusConstructionAt j y b hjy Q)
    (f : X ⟶ Y) (hxy : f x = y)
    (hPQ : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom hxy p ∈ Q) :
    ∃ F : A ⟶ B, F a = b ∧
      Nonempty (ContinuousMap.HomotopyRel (i ≫ F).hom (f ≫ j).hom {x}) ∧
      ∀ G : A ⟶ B,
        Nonempty (ContinuousMap.HomotopyRel (i ≫ G).hom (f ≫ j).hom {x}) →
        Nonempty (ContinuousMap.HomotopyRel F.hom G.hom {a}) ∧
          Nonempty (ContinuousMap.HomotopyRel G.hom F.hom {a}) := by
  let cf := f ≫ j
  have hcf : cf x = b := (congrArg j hxy).trans hjy
  have hmap : FundamentalGroup.mapOfEq (f ≫ j).hom hcf =
      (FundamentalGroup.mapOfEq j.hom hjy).comp
        (FundamentalGroup.mapOfEq f.hom hxy) := by
    have hcomp : (j.hom.comp f.hom) x = b :=
      (congrArg (fun z : Y => j.hom z) hxy).trans hjy
    have hMap := FundamentalGroup.mapOfEq_comp (x := x) (y := y) (z := b)
      f.hom j.hom hxy hjy hcomp
    simpa only [TopCat.hom_comp] using hMap
  have hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq cf.hom rfl p = 1 := by
    intro p hp
    apply (FundamentalGroup.mapOfEq_eq_one_iff cf.hom hcf p).mp
    rw [hmap, MonoidHom.comp_apply]
    apply MonoidHom.mem_ker.mp
    rw [hj.kernel_eq]
    exact hPQ p hp
  obtain ⟨F, hFa, K, hUnique⟩ :=
    hi.exists_point_relative_extension_of_cwType hCWX hCWA B cf hkill
  exact ⟨F, hFa.trans hcf, K, hUnique⟩

/-- Two subgroup-preserving original source maps have internally derived
based plus extensions and a derived extension of their composite. Their
composite has both comparison homotopies relative to the original plus
point, and all three original source-point-relative triangles are retained.
No extension or comparison family is supplied by the caller. -/
public theorem exists_point_relative_subgroup_preserving_composition_of_cwType
    {X A Y B Z D : TopCat.{u}} [ConnectedSpace A] [ConnectedSpace B]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
    (hCWA : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ A))
    (hCWY : ∃ C : TopCat.{z}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ Y))
    (hCWB : ∃ C : TopCat.{vB}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ B))
    {i : X ⟶ A} {j : Y ⟶ B} {k : Z ⟶ D}
    {x : X} {a : A} {y : Y} {b : B} {z₀ : Z} {d₀ : D}
    {hix : i x = a} {hjy : j y = b} {hkz : k z₀ = d₀}
    [Cofibration (TopCat.const x : TopCat.of PUnit.{u + 1} ⟶ X)]
    [Cofibration (TopCat.const a : TopCat.of PUnit.{u + 1} ⟶ A)]
    [Cofibration (TopCat.const y : TopCat.of PUnit.{u + 1} ⟶ Y)]
    [Cofibration (TopCat.const b : TopCat.of PUnit.{u + 1} ⟶ B)]
    {P : Subgroup (FundamentalGroup X x)} {Q : Subgroup (FundamentalGroup Y y)}
    {R : Subgroup (FundamentalGroup Z z₀)}
    [P.Normal] [Group.IsPerfect P] [Q.Normal] [Group.IsPerfect Q]
    [R.Normal] [Group.IsPerfect R]
    (hi : TopCat.IsPlusConstructionAt i x a hix P)
    (hj : TopCat.IsPlusConstructionAt j y b hjy Q)
    (hk : TopCat.IsPlusConstructionAt k z₀ d₀ hkz R)
    (f : X ⟶ Y) (hxy : f x = y) (g : Y ⟶ Z) (hyz : g y = z₀)
    (hPQ : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom hxy p ∈ Q)
    (hQR : ∀ q ∈ Q, FundamentalGroup.mapOfEq g.hom hyz q ∈ R) :
    ∃ F : A ⟶ B, ∃ G : B ⟶ D, ∃ T : A ⟶ D,
      F a = b ∧ G b = d₀ ∧ T a = d₀ ∧ (F ≫ G) a = d₀ ∧
        Nonempty (ContinuousMap.HomotopyRel (i ≫ F).hom (f ≫ j).hom {x}) ∧
        Nonempty (ContinuousMap.HomotopyRel (j ≫ G).hom (g ≫ k).hom {y}) ∧
        Nonempty (ContinuousMap.HomotopyRel (i ≫ T).hom ((f ≫ g) ≫ k).hom {x}) ∧
        Nonempty (ContinuousMap.HomotopyRel (F ≫ G).hom T.hom {a}) ∧
        Nonempty (ContinuousMap.HomotopyRel T.hom (F ≫ G).hom {a}) := by
  obtain ⟨F, hFa, ⟨KF⟩, _⟩ :=
    hi.exists_point_relative_subgroup_preserving_extension_of_cwType hCWX hCWA hj f hxy hPQ
  obtain ⟨G, hGb, ⟨KG⟩, _⟩ :=
    hj.exists_point_relative_subgroup_preserving_extension_of_cwType hCWY hCWB hk g hyz hQR
  have hfg : (f ≫ g) x = z₀ := (congrArg g hxy).trans hyz
  have hmap : FundamentalGroup.mapOfEq (f ≫ g).hom hfg =
      (FundamentalGroup.mapOfEq g.hom hyz).comp
        (FundamentalGroup.mapOfEq f.hom hxy) := by
    have hcomp : (g.hom.comp f.hom) x = z₀ :=
      (congrArg (fun z : Y => g.hom z) hxy).trans hyz
    have hMap := FundamentalGroup.mapOfEq_comp (x := x) (y := y) (z := z₀)
      f.hom g.hom hxy hyz hcomp
    simpa only [TopCat.hom_comp] using hMap
  have hPR : ∀ p ∈ P, FundamentalGroup.mapOfEq (f ≫ g).hom hfg p ∈ R := by
    intro p hp
    rw [hmap, MonoidHom.comp_apply]
    exact hQR _ (hPQ p hp)
  obtain ⟨T, hTa, ⟨KT⟩, hUnique⟩ :=
    hi.exists_point_relative_subgroup_preserving_extension_of_cwType
      hCWX hCWA hk (f ≫ g) hfg hPR
  let K₁ : ContinuousMap.HomotopyRel
      (i ≫ (F ≫ G)).hom (f ≫ (j ≫ G)).hom {x} :=
    ((KF.compContinuousMap G.hom).cast
      (TopCat.hom_comp (i ≫ F) G).symm
      (TopCat.hom_comp (f ≫ j) G).symm).cast
        (congrArg TopCat.Hom.hom (Category.assoc i F G))
        (congrArg TopCat.Hom.hom (Category.assoc f j G))
  let K₂ : ContinuousMap.HomotopyRel
      (f ≫ (j ≫ G)).hom ((f ≫ g) ≫ k).hom {x} :=
    (precomposePointRelative y x KG f hxy).cast rfl
      (congrArg TopCat.Hom.hom (Category.assoc f g k).symm)
  have hFGa : (F ≫ G) a = d₀ := by
    rw [TopCat.comp_app, hFa, hGb]
  obtain ⟨KTFG, KFGT⟩ := hUnique (F ≫ G) ⟨K₁.trans K₂⟩
  exact ⟨F, G, T, hFa, hGb, hTa, hFGa, ⟨KF⟩, ⟨KG⟩, ⟨KT⟩, KFGT, KTFG⟩

end TopCat.IsPlusConstructionAt

end
