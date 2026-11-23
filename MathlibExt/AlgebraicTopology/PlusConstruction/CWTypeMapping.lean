/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.ClassicalComparison
public import MathlibExt.AlgebraicTopology.PlusConstruction.SourceChange
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PiOneMapComposition
public import MathlibExt.Topology.CWComplex.SingularModel

/-!
# Maps and comparisons for independently chosen CW-type plus targets

The original source may have a genuine unbased CW model in an independent
universe. Its actual singular realization and counit reduce the proof to the
constructed classical source. All subgroups and based maps are transported
through that original counit. The independently chosen plus map is never
assumed to be a cofibration.

The extension retains an actual source homotopy triangle. Uniqueness retains
both ordinary target inverse families and both source homotopy triangles.
Range-fixed inverse families for arbitrary noncellular plus maps are not
asserted; the stronger constructed-cofibration result remains available in
ClassicalMapping. The target of the general extension may have arbitrary
components, with the actual subgroup-killing condition as input.
-/

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped ContinuousMap TopCat.modelCategory
open AlgebraicTopology AlgebraicTopology.LoopCellIndependentPlus

universe u v w z vB

namespace TopCat.IsPlusConstructionAt

private theorem descendSourceHomotopy {C X H : TopCat.{u}}
    (s : C ⟶ X) (e : C ≃ₕ X) (he : e.toFun = s.hom)
    (f g : X ⟶ H) (K : TopCat.Homotopy (s ≫ f) (s ≫ g)) :
    Nonempty (TopCat.Homotopy f g) := by
  let r : X ⟶ C := TopCat.ofHom e.invFun
  have hr : e.toFun.comp e.invFun = (r ≫ s).hom :=
    (congrArg₂ ContinuousMap.comp he (TopCat.hom_ofHom e.invFun).symm).trans
      (TopCat.hom_comp r s).symm
  let R : TopCat.Homotopy (r ≫ s) (𝟙 X) :=
    e.right_inv.some.cast hr (TopCat.hom_id (X := X)).symm
  let P : TopCat.Homotopy ((r ≫ s) ≫ f) ((r ≫ s) ≫ g) :=
    (TopCat.Homotopy.comp K (TopCat.Homotopy.refl r)).cast
      ((TopCat.hom_comp r (s ≫ f)).symm.trans
        (congrArg TopCat.Hom.hom (Category.assoc r s f).symm))
      ((TopCat.hom_comp r (s ≫ g)).symm.trans
        (congrArg TopCat.Hom.hom (Category.assoc r s g).symm))
  let RF : TopCat.Homotopy ((r ≫ s) ≫ f) f :=
    (TopCat.Homotopy.comp (TopCat.Homotopy.refl f) R).cast
      (TopCat.hom_comp (r ≫ s) f).symm
      ((TopCat.hom_comp (𝟙 X) f).symm.trans
        (congrArg TopCat.Hom.hom (Category.id_comp f)))
  let RG : TopCat.Homotopy ((r ≫ s) ≫ g) g :=
    (TopCat.Homotopy.comp (TopCat.Homotopy.refl g) R).cast
      (TopCat.hom_comp (r ≫ s) g).symm
      ((TopCat.hom_comp (𝟙 X) g).symm.trans
        (congrArg TopCat.Hom.hom (Category.id_comp g)))
  exact ⟨RF.symm.trans (P.trans RG)⟩

/-- A map out of a connected CW-type source which kills the prescribed
subgroup extends across any independently chosen connected CW-type plus map.
All source models have independent universes. The factorization and the
ordinary uniqueness homotopies are derived, without a cofibration or
comparison witness for the chosen plus map. -/
public theorem exists_extension_of_cwType
    {X A : TopCat.{u}} [ConnectedSpace A]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
    (hCWA : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ A))
    {i : X ⟶ A} {x : X} {a : A} {hix : i x = a}
    {P : Subgroup (FundamentalGroup X x)} [P.Normal] [Group.IsPerfect P]
    (hi : TopCat.IsPlusConstructionAt i x a hix P)
    (H : TopCat.{u}) (f : X ⟶ H)
    (hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom rfl p = 1) :
    ∃ F : A ⟶ H, Nonempty (TopCat.Homotopy (i ≫ F) f) ∧
      ∀ G : A ⟶ H, Nonempty (TopCat.Homotopy (i ≫ G) f) →
        Nonempty (TopCat.Homotopy F G) ∧ Nonempty (TopCat.Homotopy G F) := by
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
  letI : Cofibration iC := originalInclusion_cofibration C c Q
  obtain ⟨T, hT, eT, heT, G, hL, _, hSG, _⟩ :=
    original_connected_CW_plus_comparison C c Q A ⟨CA, hTA, hCA, ⟨eA⟩⟩
      (s ≫ i) a ((congrArg i hs).trans hix) hiC
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
  have hsource : ((s ≫ i) ≫ G) ≫ Fc = s ≫ (i ≫ F) := by
    dsimp only [F]
    simp only [Category.assoc]
  let KC : TopCat.Homotopy (s ≫ (i ≫ F)) (s ≫ f) :=
    (TopCat.Homotopy.comp (TopCat.Homotopy.refl Fc) hSG.some).cast
      ((TopCat.hom_comp ((s ≫ i) ≫ G) Fc).symm.trans
        (congrArg TopCat.Hom.hom hsource))
      ((TopCat.hom_comp iC Fc).symm.trans
        (congrArg TopCat.Hom.hom hFc))
  obtain ⟨eX, heX⟩ := TopCat.singularRealizationHomotopyEquiv_of_CWType X hCWX
  refine ⟨F, descendSourceHomotopy s eX heX (i ≫ F) f KC, ?_⟩
  intro G₀ hG₀
  let KP := TopCat.Homotopy.comp hG₀.some (TopCat.Homotopy.refl s)
  have hstart : iC ≫ (T ≫ G₀) = s ≫ (i ≫ G₀) :=
    (Category.assoc iC T G₀).symm.trans
      ((congrArg (fun k => k ≫ G₀) hT).trans (Category.assoc s i G₀))
  let KR : TopCat.Homotopy (iC ≫ (T ≫ G₀)) cf :=
    KP.cast
      ((TopCat.hom_comp s (i ≫ G₀)).symm.trans
        (congrArg TopCat.Hom.hom hstart.symm))
      (TopCat.hom_comp s f).symm
  obtain ⟨R, LR, hR, _⟩ :=
    TopCat.exists_homotopyExtension_of_cofibration iC (T ≫ G₀) cf KR
  let KTF : TopCat.Homotopy (T ≫ F) Fc :=
    (TopCat.Homotopy.comp (TopCat.Homotopy.refl Fc) hL.some).cast
      ((TopCat.hom_comp (T ≫ G) Fc).symm.trans
        (congrArg TopCat.Hom.hom (Category.assoc T G Fc)))
      ((TopCat.hom_comp (𝟙 B) Fc).symm.trans
        (congrArg TopCat.Hom.hom (Category.id_comp Fc)))
  let KTG : TopCat.Homotopy (T ≫ F) (T ≫ G₀) :=
    KTF.trans ((hUnique R hR).1.some.toHomotopy.trans LR.symm)
  have hFG := descendSourceHomotopy T eT heT F G₀ KTG
  exact ⟨hFG, ⟨hFG.some.symm⟩⟩

/-- The actual subgroup-preserving source map extends to independently
chosen plus targets. The first source and plus target have genuine
independently sized CW models. The second target may have arbitrary
components; its ACTUAL based kernel gives the killing condition. Thus the
original map between CW-type sources is included without an extra target
cofibration, model comparison, or desired extension input. -/
public theorem exists_subgroupPreserving_extension_of_cwType
    {X A Y B : TopCat.{u}} [ConnectedSpace A]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
    (hCWA : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ A))
    {i : X ⟶ A} {j : Y ⟶ B} {x : X} {a : A} {y : Y} {b : B}
    {hix : i x = a} {hjy : j y = b}
    {P : Subgroup (FundamentalGroup X x)} {Q : Subgroup (FundamentalGroup Y y)}
    [P.Normal] [Group.IsPerfect P] [Q.Normal] [Group.IsPerfect Q]
    (hi : TopCat.IsPlusConstructionAt i x a hix P)
    (hj : TopCat.IsPlusConstructionAt j y b hjy Q)
    (f : X ⟶ Y) (hxy : f x = y)
    (hPQ : ∀ p ∈ P, FundamentalGroup.mapOfEq f.hom hxy p ∈ Q) :
    ∃ F : A ⟶ B, Nonempty (TopCat.Homotopy (i ≫ F) (f ≫ j)) ∧
      ∀ G : A ⟶ B, Nonempty (TopCat.Homotopy (i ≫ G) (f ≫ j)) →
        Nonempty (TopCat.Homotopy F G) ∧ Nonempty (TopCat.Homotopy G F) := by
  have hp : (f ≫ j) x = b := (congrArg j hxy).trans hjy
  have hm : FundamentalGroup.mapOfEq (f ≫ j).hom hp =
      (FundamentalGroup.mapOfEq j.hom hjy).comp
        (FundamentalGroup.mapOfEq f.hom hxy) := by
    have hcomp : (j.hom.comp f.hom) x = b :=
      (congrArg (fun z : Y => j.hom z) hxy).trans hjy
    have hMap := FundamentalGroup.mapOfEq_comp (x := x) (y := y) (z := b)
      f.hom j.hom hxy hjy hcomp
    simpa only [TopCat.hom_comp] using hMap
  have hkill : ∀ p ∈ P, FundamentalGroup.mapOfEq (f ≫ j).hom rfl p = 1 := by
    intro p hP
    apply (FundamentalGroup.mapOfEq_eq_one_iff (f ≫ j).hom hp p).mp
    rw [hm]
    have hQ : FundamentalGroup.mapOfEq f.hom hxy p ∈
        MonoidHom.ker (FundamentalGroup.mapOfEq j.hom hjy) := by
      rw [hj.kernel_eq]
      exact hPQ p hP
    exact MonoidHom.mem_ker.mp hQ
  exact hi.exists_extension_of_cwType hCWX hCWA B (f ≫ j) hkill

/-- Independently chosen connected CW-type plus targets killing the same
subgroup admit an actual homotopy equivalence over the original source in
the homotopy-triangle sense, with BOTH ordinary target inverse families and
BOTH source-triangle directions. No arbitrary plus map is a cofibration
input, and no desired comparison or inverse is supplied. -/
public theorem homotopyEquiv_of_same_subgroup_cwType
    {X A B : TopCat.{u}} [ConnectedSpace A] [ConnectedSpace B]
    (hCWX : ∃ C : TopCat.{v}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ X))
    (hCWA : ∃ C : TopCat.{w}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ A))
    (hCWB : ∃ C : TopCat.{z}, ∃ _ : T2Space C,
      ∃ _ : Topology.CWComplex (Set.univ : Set C), Nonempty (C ≃ₕ B))
    {i : X ⟶ A} {j : X ⟶ B} {x : X} {a : A} {b : B}
    {hix : i x = a} {hjx : j x = b}
    {P : Subgroup (FundamentalGroup X x)} [P.Normal] [Group.IsPerfect P]
    (hi : TopCat.IsPlusConstructionAt i x a hix P)
    (hj : TopCat.IsPlusConstructionAt j x b hjx P) :
    ∃ F : A ⟶ B, ∃ G : B ⟶ A, ∃ e : A ≃ₕ B,
      e.toFun = F.hom ∧ e.invFun = G.hom ∧
        Nonempty (TopCat.Homotopy (F ≫ G) (𝟙 A)) ∧
        Nonempty (TopCat.Homotopy (G ≫ F) (𝟙 B)) ∧
        Nonempty (TopCat.Homotopy (i ≫ F) j) ∧
        Nonempty (TopCat.Homotopy (j ≫ G) i) := by
  have hkillI : ∀ p ∈ P, FundamentalGroup.mapOfEq i.hom rfl p = 1 := by
    intro p hP
    apply (FundamentalGroup.mapOfEq_eq_one_iff i.hom hix p).mp
    apply MonoidHom.mem_ker.mp
    rw [hi.kernel_eq]
    exact hP
  have hkillJ : ∀ p ∈ P, FundamentalGroup.mapOfEq j.hom rfl p = 1 := by
    intro p hP
    apply (FundamentalGroup.mapOfEq_eq_one_iff j.hom hjx p).mp
    apply MonoidHom.mem_ker.mp
    rw [hj.kernel_eq]
    exact hP
  obtain ⟨F, hF, _⟩ := hi.exists_extension_of_cwType hCWX hCWA B j hkillJ
  obtain ⟨G, hG, _⟩ := hj.exists_extension_of_cwType hCWX hCWB A i hkillI
  let KF := hF.some
  let KG := hG.some
  let KFA : TopCat.Homotopy (i ≫ (F ≫ G)) i :=
    ((TopCat.Homotopy.comp (TopCat.Homotopy.refl G) KF).cast
      ((TopCat.hom_comp (i ≫ F) G).symm.trans
        (congrArg TopCat.Hom.hom (Category.assoc i F G)))
      (TopCat.hom_comp j G).symm).trans KG
  let KGB : TopCat.Homotopy (j ≫ (G ≫ F)) j :=
    ((TopCat.Homotopy.comp (TopCat.Homotopy.refl F) KG).cast
      ((TopCat.hom_comp (j ≫ G) F).symm.trans
        (congrArg TopCat.Hom.hom (Category.assoc j G F)))
      (TopCat.hom_comp i F).symm).trans KF
  obtain ⟨_, _, uA⟩ := hi.exists_extension_of_cwType hCWX hCWA A i hkillI
  obtain ⟨_, _, uB⟩ := hj.exists_extension_of_cwType hCWX hCWB B j hkillJ
  have hIA : Nonempty (TopCat.Homotopy (i ≫ 𝟙 A) i) :=
    ⟨(TopCat.Homotopy.refl i).cast (congrArg TopCat.Hom.hom (Category.comp_id i).symm) rfl⟩
  have hIB : Nonempty (TopCat.Homotopy (j ≫ 𝟙 B) j) :=
    ⟨(TopCat.Homotopy.refl j).cast (congrArg TopCat.Hom.hom (Category.comp_id j).symm) rfl⟩
  let LA : TopCat.Homotopy (F ≫ G) (𝟙 A) :=
    (uA (F ≫ G) ⟨KFA⟩).1.some.symm.trans ((uA (𝟙 A) hIA).1.some)
  let LB : TopCat.Homotopy (G ≫ F) (𝟙 B) :=
    (uB (G ≫ F) ⟨KGB⟩).1.some.symm.trans ((uB (𝟙 B) hIB).1.some)
  let e : A ≃ₕ B :=
    { toFun := F.hom
      invFun := G.hom
      left_inv := ⟨LA.cast (TopCat.hom_comp F G) (TopCat.hom_id (X := A))⟩
      right_inv := ⟨LB.cast (TopCat.hom_comp G F) (TopCat.hom_id (X := B))⟩ }
  exact ⟨F, G, e, rfl, rfl, ⟨LA⟩, ⟨LB⟩, hF, hG⟩

/-- Subgroup-preserving original source maps have internally derived plus
extensions and an extension of their composite, with all three original
source triangles and comparison homotopies in both directions. The chosen
plus maps need not be cofibrations; no extension, inverse or homotopy
witness is supplied, and no source-point cofibrancy is required. -/
public theorem exists_subgroup_preserving_composition_of_cwType
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
      Nonempty (TopCat.Homotopy (i ≫ F) (f ≫ j)) ∧
        Nonempty (TopCat.Homotopy (j ≫ G) (g ≫ k)) ∧
        Nonempty (TopCat.Homotopy (i ≫ T) ((f ≫ g) ≫ k)) ∧
        Nonempty (TopCat.Homotopy (F ≫ G) T) ∧
        Nonempty (TopCat.Homotopy T (F ≫ G)) := by
  obtain ⟨F, ⟨KF⟩, _⟩ :=
    hi.exists_subgroupPreserving_extension_of_cwType hCWX hCWA hj f hxy hPQ
  obtain ⟨G, ⟨KG⟩, _⟩ :=
    hj.exists_subgroupPreserving_extension_of_cwType hCWY hCWB hk g hyz hQR
  have hfg : (f ≫ g) x = z₀ := (congrArg g hxy).trans hyz
  have hm : FundamentalGroup.mapOfEq (f ≫ g).hom hfg =
      (FundamentalGroup.mapOfEq g.hom hyz).comp
        (FundamentalGroup.mapOfEq f.hom hxy) := by
    have hcomp : (g.hom.comp f.hom) x = z₀ :=
      (congrArg (fun z : Y => g.hom z) hxy).trans hyz
    have hMap := FundamentalGroup.mapOfEq_comp (x := x) (y := y) (z := z₀)
      f.hom g.hom hxy hyz hcomp
    simpa only [TopCat.hom_comp] using hMap
  have hPR : ∀ p ∈ P, FundamentalGroup.mapOfEq (f ≫ g).hom hfg p ∈ R := by
    intro p hp
    rw [hm, MonoidHom.comp_apply]
    exact hQR _ (hPQ p hp)
  obtain ⟨T, ⟨KT⟩, hUnique⟩ :=
    hi.exists_subgroupPreserving_extension_of_cwType hCWX hCWA hk (f ≫ g) hfg hPR
  let K₁ : TopCat.Homotopy (i ≫ (F ≫ G)) (f ≫ (j ≫ G)) :=
    (TopCat.Homotopy.comp (TopCat.Homotopy.refl G) KF).cast
      ((TopCat.hom_comp (i ≫ F) G).symm.trans
        (congrArg TopCat.Hom.hom (Category.assoc i F G)))
      ((TopCat.hom_comp (f ≫ j) G).symm.trans
        (congrArg TopCat.Hom.hom (Category.assoc f j G)))
  let K₂ : TopCat.Homotopy (f ≫ (j ≫ G)) ((f ≫ g) ≫ k) :=
    (TopCat.Homotopy.comp KG (TopCat.Homotopy.refl f)).cast
      (TopCat.hom_comp f (j ≫ G)).symm
      ((TopCat.hom_comp f (g ≫ k)).symm.trans
        (congrArg TopCat.Hom.hom (Category.assoc f g k).symm))
  obtain ⟨KTFG, KFGT⟩ := hUnique (F ≫ G) ⟨K₁.trans K₂⟩
  exact ⟨F, G, T, ⟨KF⟩, ⟨KG⟩, ⟨KT⟩, KFGT, KTFG⟩

end TopCat.IsPlusConstructionAt

end
