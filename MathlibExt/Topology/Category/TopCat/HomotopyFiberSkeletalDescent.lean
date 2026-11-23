/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberSkeletalRestriction
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationQuillenEquivalence
import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
import Mathlib.CategoryTheory.MorphismProperty.WeakFactorizationSystem
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Descent through actual skeletal homotopy-fiber restrictions

Compact-family factorization supplies the actual singular colimit cocone.
Weak canonical comparisons at the stages supply weak actual transition maps.
Their monomorphism property makes them trivial cofibrations. Sequential
composition then proves the actual map from a stage to the original fiber weak.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial

universe u v w

namespace HomotopicalAlgebra

private theorem sequentialCocone_trivialCofibration
    {C : Type u} [Category.{v} C] [ModelCategory C]
    (F : ℕ ⥤ C) (c : Cocone F) (hc : IsColimit c)
    (hstep : ∀ n : ℕ, trivialCofibrations C (F.map (homOfLE (Nat.le_succ n)))) :
    trivialCofibrations C (c.ι.app 0) := by
  have hEq : (fibrations C).llp = trivialCofibrations C :=
    MorphismProperty.llp_eq_of_wfs (trivialCofibrations C) (fibrations C)
  let _ : (trivialCofibrations C).IsStableUnderTransfiniteCompositionOfShape ℕ := by
    rw [← hEq]
    infer_instance
  let t : (trivialCofibrations C).TransfiniteCompositionOfShape ℕ (c.ι.app 0) :=
    { F := F
      isoBot := Iso.refl _
      incl := c.ι
      isColimit := hc
      map_mem := fun n _ => hstep n }
  exact (MorphismProperty.transfiniteCompositionsOfShape_le (trivialCofibrations C) ℕ) _ t.mem

end HomotopicalAlgebra

namespace SSet

open scoped SSet.modelCategoryQuillen

private theorem sequentialCocone_weak_of_mono_weak
    (F : ℕ ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (hm : ∀ n : ℕ, Mono (F.map (homOfLE (Nat.le_succ n))))
    (hw : ∀ n : ℕ, WeakEquivalence (F.map (homOfLE (Nat.le_succ n)))) :
    WeakEquivalence (c.ι.app 0) := by
  have ht : ∀ n : ℕ, trivialCofibrations SSet.{u} (F.map (homOfLE (Nat.le_succ n))) := by
    intro n
    let _ : Mono (F.map (homOfLE (Nat.le_succ n))) := hm n
    let _ : Cofibration (F.map (homOfLE (Nat.le_succ n))) :=
      modelCategoryQuillen.cofibration_of_mono _
    let _ : WeakEquivalence (F.map (homOfLE (Nat.le_succ n))) := hw n
    exact mem_trivialCofibrations _
  exact ((mem_trivialCofibrations_iff _).mp
    (HomotopicalAlgebra.sequentialCocone_trivialCofibration F c hc ht)).2

end SSet

namespace TopCat

private theorem skeletalCarrierLE {X : SSet.{u}} {A : X.Subcomplex} {d₀ : ℕ}
    (hA₀ : A ≤ X.skeleton d₀) (n : ℕ) : A ≤ X.skeleton (d₀ + n) :=
  hA₀.trans (X.skeleton.monotone (Nat.le_add_right d₀ n))

private abbrev skeletalHomotopyFiberStage {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A : X.Subcomplex} {d₀ : ℕ}
    (hA₀ : A ≤ X.skeleton d₀) (a : SSet.toTop.obj (A : SSet.{u})) (n : ℕ) : TopCat.{u} :=
  homotopyFiber (pullback.snd p (SSet.toTop.map (X.skeleton (d₀ + n)).ι))
    (SSet.toTop.map (SSet.Subcomplex.homOfLE (skeletalCarrierLE hA₀ n)) a)

private def skeletalHomotopyFiberDiagram {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A : X.Subcomplex} {d₀ : ℕ}
    (hA₀ : A ≤ X.skeleton d₀) (a : SSet.toTop.obj (A : SSet.{u})) : ℕ ⥤ TopCat.{u} where
  obj n := skeletalHomotopyFiberStage p hA₀ a n
  map {n m} f := subcomplexHomotopyFiberTransition p (skeletalCarrierLE hA₀ n)
    (X.skeleton.monotone (Nat.add_le_add_left (leOfHom f) d₀)) a
  map_id n := by
    apply (cancel_mono (subcomplexHomotopyFiberMap p (skeletalCarrierLE hA₀ n) a)).mp
    rw [Category.id_comp]
    exact subcomplexHomotopyFiberTransition_map p (skeletalCarrierLE hA₀ n)
      (X.skeleton.monotone (Nat.add_le_add_left (leOfHom (𝟙 n)) d₀)) a
  map_comp {n m k} f g := by
    apply (cancel_mono (subcomplexHomotopyFiberMap p (skeletalCarrierLE hA₀ k) a)).mp
    rw [Category.assoc, subcomplexHomotopyFiberTransition_map,
      subcomplexHomotopyFiberTransition_map, subcomplexHomotopyFiberTransition_map]

private def skeletalHomotopyFiberCocone {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A : X.Subcomplex} {d₀ : ℕ}
    (hA₀ : A ≤ X.skeleton d₀) (a : SSet.toTop.obj (A : SSet.{u})) :
    Cocone (skeletalHomotopyFiberDiagram p hA₀ a) where
  pt := homotopyFiber p (SSet.toTop.map A.ι a)
  ι :=
    { app n := subcomplexHomotopyFiberMap p (skeletalCarrierLE hA₀ n) a
      naturality n m f := by
        exact subcomplexHomotopyFiberTransition_map p (skeletalCarrierLE hA₀ n)
          (X.skeleton.monotone (Nat.add_le_add_left (leOfHom f) d₀)) a }

private def skeletalSingHomotopyFiberCocone {E : TopCat.{u}} {X : SSet.{u}}
    (p : E ⟶ SSet.toTop.obj X) {A : X.Subcomplex} {d₀ : ℕ}
    (hA₀ : A ≤ X.skeleton d₀) (a : SSet.toTop.obj (A : SSet.{u})) :
    Cocone (skeletalHomotopyFiberDiagram p hA₀ a ⋙ TopCat.toSSet) :=
  TopCat.toSSet.mapCocone (skeletalHomotopyFiberCocone p hA₀ a)

private theorem skeletalSingHomotopyFiber_jointly_surjective
    {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    {A : X.Subcomplex} [SSet.Finite (A : SSet.{u})] {d₀ : ℕ}
    (hA₀ : A ≤ X.skeleton d₀) (a : SSet.toTop.obj (A : SSet.{u}))
    (n : ℕ) (z : (TopCat.toSSet.obj (homotopyFiber p (SSet.toTop.map A.ι a))).obj
      (Opposite.op ⦋n⦌)) :
    ∃ (k : ℕ) (y : (TopCat.toSSet.obj (skeletalHomotopyFiberStage p hA₀ a k)).obj
      (Opposite.op ⦋n⦌)),
      z = ((skeletalSingHomotopyFiberCocone p hA₀ a).ι.app k).app (Opposite.op ⦋n⦌) y := by
  let T : SSet.{u} := Δ[n]
  let H : TopCat.{u} := homotopyFiber p (SSet.toTop.map A.ι a)
  let f : SSet.toTop.obj T ⟶ H :=
    (sSetTopAdj.homEquiv T H).symm (SSet.yonedaEquiv.symm z)
  let _ : CompactSpace (SSet.toTop.obj T) := inferInstance
  obtain ⟨d, hd₀, hAd, g, hg⟩ := exists_skeleton_homotopyFiber_factor p A a d₀ f
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd₀
  let g' : SSet.toTop.obj T ⟶ skeletalHomotopyFiberStage p hA₀ a k := g
  let leg := (skeletalHomotopyFiberCocone p hA₀ a).ι.app k
  have hg' : g' ≫ leg = f := hg
  let η : T ⟶ TopCat.toSSet.obj (skeletalHomotopyFiberStage p hA₀ a k) :=
    sSetTopAdj.homEquiv T _ g'
  let y := SSet.yonedaEquiv η
  have hη : η ≫ TopCat.toSSet.map leg = SSet.yonedaEquiv.symm z := by
    have hnat : sSetTopAdj.homEquiv T H (g' ≫ leg) = η ≫ TopCat.toSSet.map leg :=
      sSetTopAdj.homEquiv_naturality_right g' leg
    have hcode : sSetTopAdj.homEquiv T H f = SSet.yonedaEquiv.symm z := by
      dsimp only [f]
      exact (sSetTopAdj.homEquiv T H).apply_symm_apply _
    exact hnat.symm.trans ((congrArg (sSetTopAdj.homEquiv T H) hg').trans hcode)
  refine ⟨k, y, ?_⟩
  change z = (TopCat.toSSet.map leg).app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv η)
  have hy := congrArg (fun e : T ⟶ TopCat.toSSet.obj H => SSet.yonedaEquiv e) hη
  dsimp only [H] at hy
  have hzero : SSet.yonedaEquiv (SSet.yonedaEquiv.symm z) = z :=
    SSet.yonedaEquiv.apply_symm_apply z
  have hz : z = SSet.yonedaEquiv (η ≫ TopCat.toSSet.map leg) := hzero.symm.trans hy.symm
  exact hz.trans (SSet.yonedaEquiv_comp η (TopCat.toSSet.map leg))

private theorem singularMap_app_injective_of_mono {Y Z : TopCat.{u}}
    (f : Y ⟶ Z) [Mono f] (n : ℕ) :
    Function.Injective ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌)) := by
  have hf := (TopCat.mono_iff_injective f).mp inferInstance
  intro x y h
  apply (Y.toSSetObjEquiv (Opposite.op ⦋n⦌)).injective
  ext t
  have hc := congrArg (Z.toSSetObjEquiv (Opposite.op ⦋n⦌)) h
  have ht := DFunLike.congr_fun hc t
  exact hf ht

private noncomputable def skeletalSingHomotopyFiber_isColimit
    {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    {A : X.Subcomplex} [SSet.Finite (A : SSet.{u})] {d₀ : ℕ}
    (hA₀ : A ≤ X.skeleton d₀) (a : SSet.toTop.obj (A : SSet.{u})) :
    IsColimit (skeletalSingHomotopyFiberCocone p hA₀ a) := by
  refine evaluationJointlyReflectsColimits _ (fun b => ?_)
  obtain ⟨⟨n⟩⟩ := b
  let c := (SSet.evaluation.obj (Opposite.op ⦋n⦌)).mapCocone
    (skeletalSingHomotopyFiberCocone p hA₀ a)
  change IsColimit c
  apply Types.FilteredColimit.isColimitOf' _ c
  · exact skeletalSingHomotopyFiber_jointly_surjective p hA₀ a n
  · intro k x y h
    have hi := singularMap_app_injective_of_mono
      (subcomplexHomotopyFiberMap p (skeletalCarrierLE hA₀ k) a) n
    refine ⟨k, 𝟙 k, ?_⟩
    have hxy : x = y := hi h
    exact congrArg _ hxy

private theorem singularMap_mono_of_mono {Y Z : TopCat.{u}} (f : Y ⟶ Z) [Mono f] :
    Mono (TopCat.toSSet.map f) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨n⟩⟩
  exact (CategoryTheory.mono_iff_injective _).mpr (singularMap_app_injective_of_mono f n)

open scoped SSet.modelCategoryQuillen

private theorem singularMap_weak_of_weak {Y Z : TopCat.{u}} (f : Y ⟶ Z)
    (hf : weakHomotopyEquivalences f) : WeakEquivalence (TopCat.toSSet.map f) := by
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) := TopCat.toSSet_obj_kanComplex Y
  let _ : SSet.KanComplex (TopCat.toSSet.obj Z) := TopCat.toSSet_obj_kanComplex Z
  exact (weakEquivalence_iff _).mpr
    ((SSet.KanComplex.W_iff_realizationWeakEquivalence (TopCat.toSSet.map f)).mp
      ((TopCat.mem_weakHomotopyEquivalences_iff f).mp hf))

private theorem weak_of_singularMap_weak {Y Z : TopCat.{u}} (f : Y ⟶ Z)
    (hf : WeakEquivalence (TopCat.toSSet.map f)) : weakHomotopyEquivalences f := by
  let _ : SSet.KanComplex (TopCat.toSSet.obj Y) := TopCat.toSSet_obj_kanComplex Y
  let _ : SSet.KanComplex (TopCat.toSSet.obj Z) := TopCat.toSSet_obj_kanComplex Z
  exact (TopCat.mem_weakHomotopyEquivalences_iff f).mpr
    ((SSet.KanComplex.W_iff_realizationWeakEquivalence (TopCat.toSSet.map f)).mpr
      ((weakEquivalence_iff _).mp hf))

/-- The actual map from the initial skeletal homotopy fiber to the original
fiber is weak when the canonical comparisons at all later stages are weak.
Its singular colimit and weak cocone leg are derived from compact factorization. -/
theorem subcomplexHomotopyFiberMap_mem_of_skeletalRestrictions
    {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    (A : X.Subcomplex) [SSet.Finite (A : SSet.{u})] (a : SSet.toTop.obj (A : SSet.{u}))
    {d₀ : ℕ} (hA₀ : A ≤ X.skeleton d₀)
    (hstage : ∀ n : ℕ, weakHomotopyEquivalences (strictFiberToHomotopyFiber
      (pullback.snd p (SSet.toTop.map (X.skeleton (d₀ + n)).ι))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE
        (hA₀.trans (X.skeleton.monotone (Nat.le_add_right d₀ n)))) a))) :
    weakHomotopyEquivalences (subcomplexHomotopyFiberMap p hA₀ a) := by
  let F := skeletalHomotopyFiberDiagram p hA₀ a ⋙ TopCat.toSSet
  let c := skeletalSingHomotopyFiberCocone p hA₀ a
  have hc : IsColimit c := skeletalSingHomotopyFiber_isColimit p hA₀ a
  have hm : ∀ n : ℕ, Mono (F.map (homOfLE (Nat.le_succ n))) := by
    intro n
    change Mono (TopCat.toSSet.map (subcomplexHomotopyFiberTransition p (skeletalCarrierLE hA₀ n)
      (X.skeleton.monotone (Nat.add_le_add_left (Nat.le_succ n) d₀)) a))
    exact singularMap_mono_of_mono _
  have hw : ∀ n : ℕ, WeakEquivalence (F.map (homOfLE (Nat.le_succ n))) := by
    intro n
    change WeakEquivalence (TopCat.toSSet.map
      (subcomplexHomotopyFiberTransition p (skeletalCarrierLE hA₀ n)
        (X.skeleton.monotone (Nat.add_le_add_left (Nat.le_succ n) d₀)) a))
    apply singularMap_weak_of_weak
    exact subcomplexHomotopyFiberTransition_mem_of_comparisons p (skeletalCarrierLE hA₀ n)
      (X.skeleton.monotone (Nat.add_le_add_left (Nat.le_succ n) d₀)) a (hstage n) (hstage (n + 1))
  have wsing : WeakEquivalence (TopCat.toSSet.map (subcomplexHomotopyFiberMap p hA₀ a)) :=
    SSet.sequentialCocone_weak_of_mono_weak F c hc hm hw
  exact weak_of_singularMap_weak _ wsing

/-- Canonical stage comparisons imply the original comparison at a fixed
finite carrier point, using the derived weak actual stage-to-global map. -/
theorem strictFiberToHomotopyFiber_mem_of_skeletalRestrictions
    {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    (A : X.Subcomplex) [SSet.Finite (A : SSet.{u})] (a : SSet.toTop.obj (A : SSet.{u}))
    {d₀ : ℕ} (hA₀ : A ≤ X.skeleton d₀)
    (hstage : ∀ n : ℕ, weakHomotopyEquivalences (strictFiberToHomotopyFiber
      (pullback.snd p (SSet.toTop.map (X.skeleton (d₀ + n)).ι))
      (SSet.toTop.map (SSet.Subcomplex.homOfLE
        (hA₀.trans (X.skeleton.monotone (Nat.le_add_right d₀ n)))) a))) :
    weakHomotopyEquivalences (strictFiberToHomotopyFiber p (SSet.toTop.map A.ι a)) :=
  strictFiberToHomotopyFiber_mem_of_subcomplexRestriction p hA₀ a (hstage 0)
    (subcomplexHomotopyFiberMap_mem_of_skeletalRestrictions p A a hA₀ hstage)

/-- Quasifibration descent over the actual simplicial skeletons, at every
original base point. Mathlib's bound `n + 1` is the topological `n`-skeleton;
the canonical stage comparisons are the induction hypotheses. -/
theorem strictFiberToHomotopyFiber_mem_of_skeletons
    {E : TopCat.{u}} {X : SSet.{u}} (p : E ⟶ SSet.toTop.obj X)
    (hstage : ∀ (n : ℕ) (b : SSet.toTop.obj (X.skeleton (n + 1) : SSet.{u})),
      weakHomotopyEquivalences (strictFiberToHomotopyFiber
        (pullback.snd p (SSet.toTop.map (X.skeleton (n + 1)).ι)) b))
    (b : SSet.toTop.obj X) : weakHomotopyEquivalences (strictFiberToHomotopyFiber p b) := by
  have hstage' : ∀ (d : ℕ) (a : SSet.toTop.obj (X.skeleton d : SSet.{u})),
      weakHomotopyEquivalences (strictFiberToHomotopyFiber
        (pullback.snd p (SSet.toTop.map (X.skeleton d).ι)) a) := by
    intro d a
    cases d with
    | zero =>
        have hs : IsInitial (X.skeleton 0 : SSet.{u}) := by
          rw [X.skeleton_zero]
          exact SSet.Subcomplex.isInitialBot
        have ht : IsInitial (SSet.toTop.obj (X.skeleton 0 : SSet.{u})) :=
          hs.isInitialObj (G := SSet.toTop)
        exact PEmpty.elim ((ht.to (TopCat.of PEmpty)) a)
    | succ n => exact hstage n a
  let f : (TopCat.of PUnit : TopCat.{u}) ⟶ SSet.toTop.obj X := TopCat.const b
  obtain ⟨A, hA, g, hg⟩ := SSet.exists_finite_subcomplex_factor_topCatHom f
  let _ : SSet.Finite (A : SSet.{u}) := hA
  obtain ⟨d₀, hd₀⟩ := A.exists_le_skeleton_of_finite
  let x : (TopCat.of PUnit : TopCat.{u}) := PUnit.unit
  let a := g x
  have hb : b = SSet.toTop.map A.ι a := by
    change f x = (g ≫ SSet.toTop.map A.ι) x
    exact ConcreteCategory.congr_hom hg x
  rw [hb]
  exact strictFiberToHomotopyFiber_mem_of_skeletalRestrictions p A a hd₀
    (fun n => hstage' (d₀ + n) _)

end TopCat

end
