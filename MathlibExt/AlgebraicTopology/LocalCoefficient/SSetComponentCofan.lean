/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetBaseCoherence
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Logic.Equiv.Sum

/-!
# The original coefficient cofan on existing simplicial components

This uses the existing connected-component subcomplexes and their actual
inclusions. The coefficient maps are the original local-system pullback
chain maps. No replacement component geometry or desired componentwise
quasi-isomorphism is introduced.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe uR uX

namespace SSet

variable {R : Type uR} [CommRing R] (X : SSet.{uX}) (L : SSet.LocalSystem R X)

/-- The actual original coefficient complex on an existing π₀ component. -/
public abbrev localCoefficientComponentComplex (c : π₀ X) :
    ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
  localCoefficientChainComplex (L.pullback (π₀.component c).ι)

/-- The actual original component-to-ambient coefficient chain map. -/
public abbrev localCoefficientComponentInclusion (c : π₀ X) :
    localCoefficientComponentComplex X L c ⟶ localCoefficientChainComplex L :=
  localCoefficientPullbackChainMap (π₀.component c).ι L

/-- The cofan retains the existing component inclusions and original
coefficient transports as WHOLE chain maps. -/
public def localCoefficientComponentCofan :
    Cofan (fun c : π₀ X => localCoefficientComponentComplex X L c) :=
  Cofan.mk (localCoefficientChainComplex L) (localCoefficientComponentInclusion X L)

/-- The actual map from the coproduct of component coefficient complexes. -/
public def localCoefficientComponentCoproductMap :
    (∐ fun c : π₀ X => localCoefficientComponentComplex X L c) ⟶
      localCoefficientChainComplex L :=
  Sigma.desc (localCoefficientComponentInclusion X L)

/-- Every component map is retained exactly by the full coproduct map. -/
@[reassoc]
public theorem localCoefficientComponentCoproductMap_ι (c : π₀ X) :
    Sigma.ι (fun d : π₀ X => localCoefficientComponentComplex X L d) c ≫
        localCoefficientComponentCoproductMap X L =
      localCoefficientPullbackChainMap (π₀.component c).ι L := by
  unfold localCoefficientComponentCoproductMap
  rw [Sigma.ι_comp_desc]

/-- The existing canonical component label of an original simplex. -/
private def componentSimplexLabel (n : ℕ) (σ : X _⦋n⦌) : π₀ X :=
  π₀.mk (X.map (⦋0⦌.const ⦋n⦌ 0).op σ)

/-- The existing component simplices partition the original simplex set. -/
private def componentSimplexEquiv (n : ℕ) :
    (Σ c : π₀ X, (π₀.component c : SSet.{uX}) _⦋n⦌) ≃ X _⦋n⦌ :=
  Equiv.sigmaFiberEquiv (componentSimplexLabel X n)

/-- The ACTUAL degree map from component chains is an Iso. The index
equivalence is the existing simplex partition, and the coefficient factors
are the original pullback-family equality transports. -/
public theorem localCoefficientComponentCoproductMap_f_isIso (n : ℕ) :
    IsIso ((localCoefficientComponentCoproductMap X L).f n) := by
  let K : π₀ X → ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
    localCoefficientComponentComplex X L
  let ev := HomologicalComplex.eval (ModuleCat.{max uR uX} R) (ComplexShape.down ℕ) n
  let I : π₀ X → Type uX :=
    fun c => (π₀.component c : SSet.{uX}) _⦋n⦌
  let F : (c : π₀ X) → I c → ModuleCat.{max uR uX} R :=
    fun c => localCoefficientFamily (L.pullback (π₀.component c).ι) n
  let G := localCoefficientFamily L n
  let e := componentSimplexEquiv X n
  let w : ∀ p : Σ c : π₀ X, I c, G (e p) ≅ F p.1 p.2 :=
    fun p => (eqToIso (localCoefficientPullbackFamilyEq (π₀.component p.1).ι L p.2)).symm
  let eX : (∐ fun c : π₀ X => (K c).X n) ≅ (∐ fun c : π₀ X => ∐ F c) :=
    Sigma.mapIso (fun c => eqToIso (localCoefficientChainComplex_X
      (L.pullback (π₀.component c).ι) n))
  let E : (∐ fun c : π₀ X => (K c).X n) ≅ localCoefficientObj L n :=
    eX ≪≫ sigmaSigmaIso I F ≪≫ Sigma.whiskerEquiv e w
  let s := sigmaComparison ev K
  have hE : s ≫ (localCoefficientComponentCoproductMap X L).f n =
      E.hom ≫ (eqToIso (localCoefficientChainComplex_X L n)).inv := by
    apply Sigma.hom_ext
    intro c
    have hmap := congrArg (fun k : localCoefficientComponentComplex X L c ⟶
        localCoefficientChainComplex L => k.f n)
      (localCoefficientComponentCoproductMap_ι X L c)
    simp only [HomologicalComplex.comp_f] at hmap
    have hc : Sigma.ι (fun b => (K b).X n) c ≫ s ≫
        (localCoefficientComponentCoproductMap X L).f n =
          (localCoefficientPullbackChainMap (π₀.component c).ι L).f n := by
      calc
        _ = (Sigma.ι (fun b => (K b).X n) c ≫ s) ≫
            (localCoefficientComponentCoproductMap X L).f n :=
          (Category.assoc _ _ _).symm
        _ = (Sigma.ι K c).f n ≫ (localCoefficientComponentCoproductMap X L).f n :=
          congrArg (fun k => k ≫ (localCoefficientComponentCoproductMap X L).f n)
            (ι_comp_sigmaComparison ev K c)
        _ = _ := hmap
    let ec : (K c).X n ≅ localCoefficientObj (L.pullback (π₀.component c).ι) n :=
      eqToIso (localCoefficientChainComplex_X (L.pullback (π₀.component c).ι) n)
    let ea : (localCoefficientChainComplex L).X n ≅ localCoefficientObj L n :=
      eqToIso (localCoefficientChainComplex_X L n)
    apply (cancel_epi ec.inv).1
    apply Sigma.hom_ext
    intro σ
    have hcomponent := congrArg
      (fun k : (K c).X n ⟶ (localCoefficientChainComplex L).X n =>
        (Sigma.ι (F c) σ ≫ ec.inv) ≫ k) hc
    simp only [Category.assoc] at hcomponent
    refine hcomponent.trans ?_
    let p : Σ d : π₀ X, I d := ⟨c, σ⟩
    let ss := sigmaSigmaIso I F
    let we := Sigma.whiskerEquiv e w
    have hiX : Sigma.ι (fun d => (K d).X n) c ≫ eX.hom =
        ec.hom ≫ Sigma.ι (fun d => ∐ F d) c := by
      exact Sigma.ι_mapIso_hom
        (fun d => eqToIso (localCoefficientChainComplex_X
          (L.pullback (π₀.component d).ι) n)) c
    have hiE : Sigma.ι (fun d => (K d).X n) c ≫ E.hom =
        ec.hom ≫ Sigma.ι (fun d => ∐ F d) c ≫ ss.hom ≫ we.hom := by
      have h := congrArg (fun k => k ≫ ss.hom ≫ we.hom) hiX
      simpa only [E, Iso.trans_hom, Category.assoc] using h
    have hchart := congrArg
      (fun k : (K c).X n ⟶ localCoefficientObj L n =>
        (Sigma.ι (F c) σ ≫ ec.inv) ≫ k) hiE
    simp only [Category.assoc, Iso.inv_hom_id_assoc] at hchart
    have hflat : Sigma.ι (F c) σ ≫ Sigma.ι (fun d => ∐ F d) c ≫ ss.hom =
        Sigma.ι (fun q : Σ d : π₀ X, I d => F q.1 q.2) p := by
      simp only [ss, sigmaSigmaIso_hom, Sigma.ι_comp_desc]
      rfl
    have hflat' := congrArg (fun k => k ≫ we.hom) hflat
    simp only [Category.assoc] at hflat'
    have hwhisker : Sigma.ι (fun q : Σ d : π₀ X, I d => F q.1 q.2) p ≫ we.hom =
        (w p).inv ≫ Sigma.ι G (e p) := by
      change Sigma.ι (fun q : Σ d : π₀ X, I d => F q.1 q.2) p ≫
        Sigma.map' e (fun q => (w q).inv) = _
      exact Sigma.ι_comp_map' e (fun q => (w q).inv) p
    have hw : (w p).inv = eqToHom (localCoefficientPullbackFamilyEq
        (π₀.component c).ι L σ) := rfl
    have hι : Sigma.ι G (e p) =
        CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (fundamentalGroupoidNerveUnit X) L ((π₀.component c).ι.app (Opposite.op ⦋n⦌) σ) :=
      rfl
    have hpoint := (congrArg (fun k => k ≫ Sigma.ι G (e p)) hw).trans
      (congrArg (fun k => eqToHom (localCoefficientPullbackFamilyEq
        (π₀.component c).ι L σ) ≫ k) hι)
    have hchart' := hchart.trans (hflat'.trans (hwhisker.trans hpoint))
    have hleft : (Sigma.ι (F c) σ ≫ ec.inv) ≫
        (localCoefficientPullbackChainMap (π₀.component c).ι L).f n ≫ ea.hom =
      eqToHom (localCoefficientPullbackFamilyEq (π₀.component c).ι L σ) ≫
        CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          (fundamentalGroupoidNerveUnit X) L ((π₀.component c).ι.app (Opposite.op ⦋n⦌) σ) :=
      localCoefficientι_pullbackChainMap_conjugate (π₀.component c).ι L n σ
    have hraw := congrArg (fun k => k ≫ ea.inv) hleft
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hraw
    have hreturn := congrArg (fun k => k ≫ ea.inv) hchart'
    simp only [Category.assoc] at hreturn
    exact hraw.trans hreturn.symm
  let : IsIso (s ≫ (localCoefficientComponentCoproductMap X L).f n) := by
    rw [hE]
    infer_instance
  exact (isIso_comp_left_iff s _).mp inferInstance

/-- The original coefficient chains are the coproduct of their EXISTING
component chains, with every component map retained as a WHOLE chain map. -/
public theorem localCoefficientComponentCoproductMap_isIso :
    IsIso (localCoefficientComponentCoproductMap X L) := by
  let (n : ℕ) : IsIso ((localCoefficientComponentCoproductMap X L).f n) :=
    localCoefficientComponentCoproductMap_f_isIso X L n
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The original component coefficient cofan is colimiting. -/
public def isColimitLocalCoefficientComponentCofan :
    IsColimit (localCoefficientComponentCofan X L) := by
  have h : IsIso (localCoefficientComponentCoproductMap X L) :=
    localCoefficientComponentCoproductMap_isIso X L
  have hd : Sigma.desc (localCoefficientComponentCofan X L).inj =
      localCoefficientComponentCoproductMap X L := rfl
  letI : IsIso (Sigma.desc (localCoefficientComponentCofan X L).inj) := hd.symm ▸ h
  exact Cofan.isColimitOfIsIsoSigmaDesc _

end SSet

end
