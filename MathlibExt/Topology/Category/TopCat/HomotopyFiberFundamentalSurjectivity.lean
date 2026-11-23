/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.PlusConstruction.Basic
public import MathlibExt.AlgebraicTopology.SingularHomology.IntegralReducedConnectivity
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberLoops
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.LoopRepresentatives
public import MathlibExt.AlgebraicTopology.FundamentalGroupoid.PathTransportNaturality
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Fundamental-group surjectivity from the original acyclic ending fiber

The chosen source point gives an actual point of the ending-path fiber.
Vanishing reduced integral H₀ makes this SAME fiber path connected.
An original target loop gives a second fiber point. A path between the
two fiber points projects to the source loop, while the complete path
family gives the original target loop through homotopy naturality.

No source/target CW structure, cofibration, fibration, Kan replacement,
path-lifting witness, or supplied fundamental-group surjection is needed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap Topology.Homotopy

universe u

namespace TopCat

private def endingFiberHomotopy {X Y : TopCat.{u}} (f : X ⟶ Y) (y : Y) :
    TopCat.Homotopy (homotopyFiberToTotal f y ≫ f) (TopCat.const y) := by
  let T := homotopyFiberToTotal f y
  let P := homotopyFiberPath f y
  have h₀ : P ≫ pathEvalZero Y = T ≫ f := homotopyPullbackPath_evalZero f (TopCat.const y)
  have h₁ : P ≫ pathEvalOne Y = TopCat.const y := by
    have h := homotopyPullbackPath_evalOne f (TopCat.const y : TopCat.of PUnit ⟶ Y)
    refine h.trans ?_
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro z
    rfl
  refine
    { toFun := fun z => P.hom z.2 ((TopCat.I.homeomorph.{u}).symm z.1)
      continuous_toFun := continuous_eval.comp
        ((P.hom.continuous.comp continuous_snd).prodMk
          ((TopCat.I.homeomorph.{u}).symm.continuous.comp continuous_fst))
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro z
    have ht : (TopCat.I.homeomorph.{u}).symm (0 : unitInterval) = (0 : TopCat.I.{u}) := by
      apply (TopCat.I.homeomorph.{u}).injective
      simp
    exact (congrArg (fun t : TopCat.I.{u} => P.hom z t) ht).trans
      (ConcreteCategory.congr_hom h₀ z)
  · intro z
    have ht : (TopCat.I.homeomorph.{u}).symm (1 : unitInterval) = (1 : TopCat.I.{u}) := by
      apply (TopCat.I.homeomorph.{u}).injective
      simp
    exact (congrArg (fun t : TopCat.I.{u} => P.hom z t) ht).trans
      (ConcreteCategory.congr_hom h₁ z)

private theorem endingFiberHomotopy_loop {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
    (γ : LoopSpace Y (f x)) (t : unitInterval) :
    (endingFiberHomotopy f (f x)).evalAt (loopToHomotopyFiber f x (f x) rfl γ) t = γ t := by
  let z := loopToHomotopyFiber f x (f x) rfl γ
  have hp := ConcreteCategory.congr_hom (loopToHomotopyFiber_path f x (f x) rfl) γ
  change homotopyFiberPath f (f x) z = loopPathObjectMap Y (f x) γ at hp
  change homotopyFiberPath f (f x) z ((TopCat.I.homeomorph.{u}).symm t) = γ t
  rw [hp]
  change γ (TopCat.I.homeomorph ((TopCat.I.homeomorph.{u}).symm t)) = γ t
  rw [(TopCat.I.homeomorph.{u}).apply_symm_apply]

private theorem constant_groupoid_map {A B : TopCat.{u}} (b : B)
    {x y : FundamentalGroupoid A} (q : x ⟶ y) :
    (FundamentalGroupoid.map (TopCat.const b : A ⟶ B).hom).map q =
      𝟙 (FundamentalGroupoid.mk b) := by
  induction q using Path.Homotopic.Quotient.ind with
  | mk p =>
    change Path.Homotopic.Quotient.mk (p.map continuous_const) =
      Path.Homotopic.Quotient.mk (Path.refl b)
    congr 1

private abbrev explicitGroupoidMap {A B : TopCat.{u}} (k : A ⟶ B) :
    FundamentalGroupoid A ⥤ FundamentalGroupoid B where
  obj a := FundamentalGroupoid.mk (k.hom a.as)
  map p := p.map k.hom
  map_id a := by
    change (FundamentalGroupoid.map k.hom).map (𝟙 a) =
      𝟙 ((FundamentalGroupoid.map k.hom).obj a)
    exact CategoryTheory.Functor.map_id _ _
  map_comp p q := by
    change (FundamentalGroupoid.map k.hom).map (p ≫ q) =
      (FundamentalGroupoid.map k.hom).map p ≫ (FundamentalGroupoid.map k.hom).map q
    exact CategoryTheory.Functor.map_comp _ _ _

/-- Path connectedness of the SAME actual ending fiber gives a preimage
of every original target fundamental-group element. -/
public theorem fundamentalGroupMap_surjective_of_pathConnected_homotopyFiber
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
    [PathConnectedSpace (homotopyFiber f (f x))] :
    Function.Surjective (FundamentalGroup.mapOfEq f.hom rfl (x := x)) := by
  let E := homotopyFiber f (f x)
  let T := homotopyFiberToTotal f (f x)
  let g : C(E, Y) := ⟨fun _ => f.hom x, continuous_const⟩
  have hg : (TopCat.const (f x) : E ⟶ Y).hom = g := rfl
  let H : ContinuousMap.Homotopy (f.hom.comp T.hom) g :=
    (endingFiberHomotopy f (f x)).cast (TopCat.hom_comp T f) hg
  let FT := explicitGroupoidMap T
  let FF := explicitGroupoidMap f
  let Q := (Functor.const (FundamentalGroupoid E)).obj (FundamentalGroupoid.mk (f.hom x))
  let η : FT ⋙ FF ⟶ Q :=
    { app := fun w => Path.Homotopic.Quotient.mk (H.evalAt w.as)
      naturality := fun {a b} p => by
        obtain ⟨r, rfl⟩ := Path.Homotopic.Quotient.mk_surjective p
        have hn := Path.Homotopic.map_trans_evalAt H r
        simp only [Functor.comp_map, FT, FF, explicitGroupoidMap,
          ← Path.Homotopic.Quotient.mk_map, Q, Functor.const_obj_map]
        dsimp only [g] at H hn ⊢
        change Path.Homotopic.Quotient.trans
            (Path.Homotopic.Quotient.mk ((r.map T.hom.continuous).map f.hom.continuous))
            (Path.Homotopic.Quotient.mk (H.evalAt b.as)) =
          Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (H.evalAt a.as))
            (Path.Homotopic.Quotient.mk (Path.refl (f.hom x)))
        rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_trans]
        have hconst : r.map g.continuous = Path.refl (f.hom x) := by
          apply _root_.Path.ext
          funext t
          rfl
        have hmap : (r.map T.hom.continuous).map f.hom.continuous =
            r.map (f.hom.comp T.hom).continuous := by
          apply _root_.Path.ext
          funext t
          rfl
        rw [hconst] at hn
        rw [hmap, Path.Homotopic.Quotient.eq]
        exact hn }
  intro q
  let γ := FundamentalGroup.loopRepresentative q
  let γ₀ : LoopSpace Y (f x) := Path.refl (f x)
  let z := loopToHomotopyFiber f x (f x) rfl γ
  let z₀ := loopToHomotopyFiber f x (f x) rfl γ₀
  let p : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk z₀ :=
    Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath z z₀)
  have hT : T z = x := ConcreteCategory.congr_hom
    (loopToHomotopyFiber_toTotal f x (f x) rfl) γ
  have hT₀ : T z₀ = x := ConcreteCategory.congr_hom
    (loopToHomotopyFiber_toTotal f x (f x) rfl) γ₀
  let c : FT.obj (FundamentalGroupoid.mk z) ≅ FundamentalGroupoid.mk x :=
    eqToIso (congrArg FundamentalGroupoid.mk hT)
  let c₀ : FT.obj (FundamentalGroupoid.mk z₀) ≅ FundamentalGroupoid.mk x :=
    eqToIso (congrArg FundamentalGroupoid.mk hT₀)
  let a : FundamentalGroup X x := End.of (c.inv ≫ FT.map p ≫ c₀.hom)
  have hc : (FF.mapIso c).hom = eqToHom (congrArg FundamentalGroupoid.mk (congrArg f.hom hT)) := by
    change FF.map (eqToHom (congrArg FundamentalGroupoid.mk hT)) = _
    exact eqToHom_map _ _
  have hc₀ : (FF.mapIso c₀).hom = eqToHom (congrArg FundamentalGroupoid.mk (congrArg f.hom hT₀)) := by
    change FF.map (eqToHom (congrArg FundamentalGroupoid.mk hT₀)) = _
    exact eqToHom_map _ _
  have hη : η.app (FundamentalGroupoid.mk z) = (FF.mapIso c).hom ≫ q.asHom := by
    have hp : HEq (η.app (FundamentalGroupoid.mk z)) q.asHom := by
      have he := Path.Homotopic.hpath_hext
        (p₁ := H.evalAt z) (p₂ := γ) (fun t => endingFiberHomotopy_loop f x γ t)
      exact he.trans (heq_of_eq (FundamentalGroup.mk_loopRepresentative q))
    have he := (conj_eqToHom_iff_heq (η.app (FundamentalGroupoid.mk z)) q.asHom
      (congrArg FundamentalGroupoid.mk (congrArg f.hom hT))
      (rfl : Q.obj (FundamentalGroupoid.mk z) = FF.obj (FundamentalGroupoid.mk x))).mpr hp
    rw [eqToHom_refl, Category.comp_id] at he
    exact he.trans (congrArg (fun w => w ≫ q.asHom) hc.symm)
  have hη₀ : η.app (FundamentalGroupoid.mk z₀) = (FF.mapIso c₀).hom := by
    have hp : HEq (η.app (FundamentalGroupoid.mk z₀)) (𝟙 (FundamentalGroupoid.mk (f x))) := by
      exact Path.Homotopic.hpath_hext (p₁ := H.evalAt z₀) (p₂ := γ₀)
        (fun t => endingFiberHomotopy_loop f x γ₀ t)
    have he := (conj_eqToHom_iff_heq (η.app (FundamentalGroupoid.mk z₀))
      (𝟙 (FundamentalGroupoid.mk (f.hom x)))
      (congrArg FundamentalGroupoid.mk (congrArg f.hom hT₀))
      (rfl : Q.obj (FundamentalGroupoid.mk z₀) = FF.obj (FundamentalGroupoid.mk x))).mpr hp
    rw [eqToHom_refl, Category.comp_id, Category.comp_id] at he
    exact he.trans hc₀.symm
  have hn := η.naturality p
  change FF.map (FT.map p) ≫ η.app (FundamentalGroupoid.mk z₀) =
    η.app (FundamentalGroupoid.mk z) ≫
      Q.map p at hn
  rw [hη, hη₀] at hn
  change FF.map (FT.map p) ≫ (FF.mapIso c₀).hom =
    ((FF.mapIso c).hom ≫ q.asHom) ≫ 𝟙 (FundamentalGroupoid.mk (f.hom x)) at hn
  rw [Category.comp_id] at hn
  simp only [Functor.mapIso_hom] at hn
  refine ⟨a, ?_⟩
  rw [FundamentalGroup.mapOfEq_rfl]
  apply End.ext
  change FF.map (c.inv ≫ FT.map p ≫ c₀.hom) = q.asHom
  calc
    FF.map (c.inv ≫ FT.map p ≫ c₀.hom) =
        FF.map c.inv ≫ (FF.map (FT.map p) ≫ FF.map c₀.hom) := by
      rw [Functor.map_comp, Functor.map_comp]
    _ = FF.map c.inv ≫ (FF.map c.hom ≫ q.asHom) := congrArg (fun k => FF.map c.inv ≫ k) hn
    _ = (FF.map c.inv ≫ FF.map c.hom) ≫ q.asHom := (Category.assoc _ _ _).symm
    _ = FF.map (c.inv ≫ c.hom) ≫ q.asHom := by rw [Functor.map_comp]
    _ = q.asHom := by rw [c.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- Canonical reduced acyclicity of the original ending fiber gives the
surjection, using its actual constant-loop point and existing H₀ connectivity. -/
public theorem fundamentalGroupMap_surjective_of_acyclic_homotopyFiber
    {X Y : TopCat.{u}} (f : X ⟶ Y) (x : X)
    (h : TopCat.IsAcyclicMapAt f (f x)) :
    Function.Surjective (FundamentalGroup.mapOfEq f.hom rfl (x := x)) := by
  let z := loopToHomotopyFiber f x (f x) rfl (Path.refl (f x))
  let : PathConnectedSpace (homotopyFiber f (f x)) :=
    TopCat.pathConnectedSpace_of_isZero_reducedIntegralH0 (homotopyFiber f (f x)) z (h 0)
  exact fundamentalGroupMap_surjective_of_pathConnected_homotopyFiber f x

/-- An arbitrary actual plus map has surjective fundamental-group map
at its specified image point. No cellular/cofibration/CW or surjectivity
witness is an additional input. -/
public theorem IsPlusConstructionAt.pi1Map_surjective
    {X Y : TopCat.{u}} {f : X ⟶ Y} {x : X} {y : Y} {hxy : f x = y}
    {P : Subgroup (FundamentalGroup X x)} [P.Normal] [Group.IsPerfect P]
    (h : TopCat.IsPlusConstructionAt f x y hxy P) :
    Function.Surjective (FundamentalGroup.mapOfEq f.hom hxy) := by
  cases hxy
  exact fundamentalGroupMap_surjective_of_acyclic_homotopyFiber f x h.acyclic

end TopCat

end
