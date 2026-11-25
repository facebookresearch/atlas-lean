/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
public import MathlibExt.CategoryTheory.MorphismProperty.WeakFactorizationSystem

/-!
# Coproducts of weak maps between cofibrant objects

Apply Brown's factorization to each original map. The two coproducts of
trivial cofibrations are trivial cofibrations by the existing lifting
class closure. The coproduct of the retractions has its original
coproduct section, so two-out-of-three gives the whole weak map.
The index universe is independent of the carrier universe.
-/

@[expose] public section

noncomputable section

universe w u v uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {J : Type w} {X : J → C}

/-- Every actual colimiting cofan of cofibrant objects is cofibrant, retaining all original legs. -/
theorem originalCofanPoint_cofibrant (c : Cofan X) (hc : IsColimit c)
    [∀ j, IsCofibrant (X j)] : IsCofibrant c.pt := by
  apply (cofibration_iff _).mpr
  rw [← trivialFibrations_llp]
  intro A B p hp
  let _ : Fibration p := (mem_trivialFibrations_iff p).mp hp |>.1
  let _ : WeakEquivalence p := (mem_trivialFibrations_iff p).mp hp |>.2
  refine ⟨fun {f} {g} sq => ?_⟩
  let squares (j : J) : CommSq (initial.to A) (initial.to (X j)) p (c.inj j ≫ g) :=
    ⟨initialIsInitial.hom_ext _ _⟩
  let lifts (j : J) : X j ⟶ A := (squares j).lift
  exact CommSq.HasLift.mk' {
    l := Cofan.IsColimit.desc hc lifts
    fac_left := initialIsInitial.hom_ext _ _
    fac_right := by
      apply hc.hom_ext
      intro j
      have hd : c.inj j.as ≫ Cofan.IsColimit.desc hc lifts = lifts j.as :=
        Cofan.IsColimit.fac hc lifts j.as
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ p) hd).trans (squares j.as).fac_right) }

end HomotopicalAlgebra

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {J : Type w} [HasCoproductsOfShape J C]

/-- The actual coproduct map is weak when every original endpoint is cofibrant and every original
map is weak. -/
theorem weakEquivalence_sigmaMap_of_cofibrant
    {X Y : J → C} (f : ∀ j, X j ⟶ Y j)
    [∀ j, IsCofibrant (X j)] [∀ j, IsCofibrant (Y j)]
    [∀ j, WeakEquivalence (f j)] : WeakEquivalence (Limits.Sigma.map f) := by
  let h : ∀ j, CofibrantBrownFactorization (f j) := fun j =>
    Classical.choice inferInstance
  let _ : (trivialCofibrations C).IsStableUnderCoproducts.{w} :=
    IsStableUnderCoproducts.of_llp_eq (trivialCofibrations C) (fibrations C)
      (fibrations_llp C)
  have hi : trivialCofibrations C (Limits.Sigma.map (fun j => (h j).i)) :=
    (trivialCofibrations C).colimMap
      (Discrete.natTrans (F := Discrete.functor X)
        (G := Discrete.functor (fun j => (h j).Z)) (fun j => (h j.as).i))
      (fun j => mem_trivialCofibrations (h j.as).i)
  have hs : trivialCofibrations C (Limits.Sigma.map (fun j => (h j).s)) :=
    (trivialCofibrations C).colimMap
      (Discrete.natTrans (F := Discrete.functor Y)
        (G := Discrete.functor (fun j => (h j).Z)) (fun j => (h j.as).s))
      (fun j => mem_trivialCofibrations (h j.as).s)
  let _ : WeakEquivalence (Limits.Sigma.map (fun j => (h j).i)) :=
    (mem_trivialCofibrations_iff _ |>.mp hi).2
  let _ : WeakEquivalence (Limits.Sigma.map (fun j => (h j).s)) :=
    (mem_trivialCofibrations_iff _ |>.mp hs).2
  have section_retraction :
      Limits.Sigma.map (fun j => (h j).s) ≫ Limits.Sigma.map (fun j => (h j).p) = 𝟙 _ := by
    rw [Limits.Sigma.map_comp_map]
    simp only [CofibrantBrownFactorization.s_p, Limits.Sigma.map_id]
  let _ : WeakEquivalence (Limits.Sigma.map (fun j => (h j).p)) :=
    weakEquivalence_of_precomp_of_fac section_retraction
  have original_factorization :
      Limits.Sigma.map (fun j => (h j).i) ≫ Limits.Sigma.map (fun j => (h j).p) = Limits.Sigma.map
          f := by
    rw [Limits.Sigma.map_comp_map]
    congr 1
    funext j
    exact (h j).fac
  rw [← original_factorization]
  infer_instance

/-- A weak family between cofibrant objects induces a weak map of the supplied genuine coproduct
cocones, with their entire original injections retained. -/
theorem weakEquivalence_of_cofibrantCoproductCocones
    {X Y : J → C} (f : ∀ j, X j ⟶ Y j)
    [∀ j, IsCofibrant (X j)] [∀ j, IsCofibrant (Y j)]
    [∀ j, WeakEquivalence (f j)]
    {cX : Cofan X} {cY : Cofan Y} (hX : IsColimit cX) (hY : IsColimit cY)
    (d : cX.pt ⟶ cY.pt) (hd : ∀ j, cX.inj j ≫ d = f j ≫ cY.inj j) :
    WeakEquivalence d := by
  let eX : (∐ X) ≅ cX.pt :=
    (colimit.isColimit (Discrete.functor X)).coconePointUniqueUpToIso hX
  let eY : (∐ Y) ≅ cY.pt :=
    (colimit.isColimit (Discrete.functor Y)).coconePointUniqueUpToIso hY
  have commutation : eX.hom ≫ d = Limits.Sigma.map f ≫ eY.hom := by
    apply Limits.Sigma.hom_ext
    intro j
    have hx : Limits.Sigma.ι X j ≫ eX.hom = cX.inj j :=
      colimit.comp_coconePointUniqueUpToIso_hom hX (Discrete.mk j)
    have hy : Limits.Sigma.ι Y j ≫ eY.hom = cY.inj j :=
      colimit.comp_coconePointUniqueUpToIso_hom hY (Discrete.mk j)
    calc
      Limits.Sigma.ι X j ≫ eX.hom ≫ d = cX.inj j ≫ d := by
        rw [← Category.assoc, hx]
      _ = f j ≫ cY.inj j := hd j
      _ = f j ≫ Limits.Sigma.ι Y j ≫ eY.hom := by rw [hy]
      _ = Limits.Sigma.ι X j ≫ Limits.Sigma.map f ≫ eY.hom := by
        rw [Limits.Sigma.ι_map_assoc]
  let _ : WeakEquivalence (Limits.Sigma.map f) :=
    weakEquivalence_sigmaMap_of_cofibrant f
  have hsigma : weakEquivalences C (Limits.Sigma.map f) := mem_weakEquivalences _
  have hdweak : weakEquivalences C d :=
    ((weakEquivalences C).arrow_mk_iso_iff (Arrow.isoMk eX eY commutation)).mp
      hsigma
  exact (weakEquivalence_iff _).mpr hdweak

end HomotopicalAlgebra
