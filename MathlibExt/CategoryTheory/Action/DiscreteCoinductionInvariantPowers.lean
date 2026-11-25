/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionShortExact
public import MathlibExt.CategoryTheory.Action.DiscreteCoinductionCoresolution
public import MathlibExt.RepresentationTheory.Homological.ContCohomology.CoinductionInvariantExactness

/-! # Exact original invariant-coinduction terms and actual monad powers -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe g w
namespace CategoryTheory.DiscreteAbelianAction
variable (G : Type g) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The original invariants functor preserves actual Hom addition. -/
instance invariants_additive : (invariantsFunctor.{g, max g w} (G := G)).Additive where
  map_add := by
    intro A B f h
    ext c
    rfl

/-- The original invariant-coinduced group is the same coefficient group by identity evaluation. -/
def coindInvariantsIso (A : DiscreteAbelianAction.{g, max g w} G) :
    invariantsFunctor.obj (coind.{g, w}.obj A) ≅ (forget.{g, max g w} G).obj A := by
  let X := toTopRep.obj A
  let hX := toTopRep_action_isContinuous A
  let e := ContinuousCohomology.coindInvariantModuleIso.{0, g, w} X hX
  let Q := forget₂ (TopModuleCat.{max g w} ℤ) (ModuleCat.{max g w} ℤ) ⋙
    forget₂ (ModuleCat.{max g w} ℤ) AddCommGrpCat.{max g w}
  exact (Q.mapIso ((TopRep.invariantsFunctor ℤ G).mapIso (coindToTopRepIso.{g, w} G A))) ≪≫
    (forget₂ (ModuleCat.{max g w} ℤ) AddCommGrpCat.{max g w}).mapIso e

/-- Evaluation has the actual identity value of the original coinduced function. -/
theorem coindInvariantsIso_hom_apply (A : DiscreteAbelianAction.{g, max g w} G)
    (c : invariantsFunctor.obj (coind.{g, w}.obj A)) :
    (coindInvariantsIso.{g, w} G A).hom c = coindFunction.{g, w} A c.val 1 := rfl

/-- The original invariant-coinduced exact sequence is the coefficient exact sequence. -/
theorem coindInvariants_shortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, max g w} G))
    (hS : (S.map (forget.{g, max g w} G)).ShortExact) :
    ((S.map coind.{g, w}).map (invariantsFunctor.{g, max g w} (G := G))).ShortExact := by
  let U := S.map (forget.{g, max g w} G)
  let T := (S.map coind.{g, w}).map (invariantsFunctor.{g, max g w} (G := G))
  let e : T ≅ U := ShortComplex.isoMk (coindInvariantsIso.{g, w} G S.X₁)
    (coindInvariantsIso.{g, w} G S.X₂) (coindInvariantsIso.{g, w} G S.X₃)
    (by ext c; rfl) (by ext c; rfl)
  exact ShortComplex.shortExact_of_iso e.symm hS

/-- Every stored actual monad power is additive through the original coinduction functor. -/
instance coindMonadPower_additive (n : ℕ) : (Monad.monadPow (coindMonad.{g, w} G) n).Additive := by
  induction n with
  | zero => change (𝟭 _).Additive; infer_instance
  | succ n ih =>
    change (coind.{g, w} ⋙ Monad.monadPow (coindMonad.{g, w} G) n).Additive
    infer_instance

/-- Zero preservation is supplied at the explicit original group and coefficient ranks. -/
instance coindMonadPower_preservesZero (n : ℕ) :
    (Monad.monadPow (coindMonad.{g, w} G) n).PreservesZeroMorphisms := by
  let : (Monad.monadPow (coindMonad.{g, w} G) n).Additive :=
    coindMonadPower_additive.{g, w} G n
  infer_instance

/-- Every actual monad power retains the given short-exact underlying coefficient sequence. -/
theorem coindPower_forget_shortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, max g w} G))
    (hS : (S.map (forget.{g, max g w} G)).ShortExact) (n : ℕ) :
    ((S.map (Monad.monadPow (coindMonad.{g, w} G) n)).map
      (forget.{g, max g w} G)).ShortExact := by
  induction n generalizing S with
  | zero => exact hS
  | succ n ih =>
    change (((S.map coind.{g, w}).map (Monad.monadPow (coindMonad.{g, w} G) n)).map
      (forget.{g, max g w} G)).ShortExact
    exact ih (S.map coind.{g, w}) (coind_forget_shortExact.{g, w} S hS)

/-- Every actual positive or zero monad power is genuinely short exact in the original category. -/
theorem coindPower_shortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, max g w} G))
    (hS : (S.map (forget.{g, max g w} G)).ShortExact) (n : ℕ) :
    (S.map (Monad.monadPow (coindMonad.{g, w} G) n)).ShortExact :=
  shortExact_of_forget_shortExact.{g, max g w} (G := G) _
    (coindPower_forget_shortExact.{g, w} G S hS n)

/-- The actual successor-power isomorphism is natural after the original invariant functor. -/
theorem coindPowerSucc_invariants_naturality (n : ℕ)
    {A B : DiscreteAbelianAction.{g, max g w} G} (f : A ⟶ B) :
    (invariantsFunctor.{g, max g w} (G := G)).map
      ((Monad.monadPow (coindMonad.{g, w} G) (n + 1)).map f) ≫
      (invariantsFunctor.{g, max g w} (G := G)).map
        (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{g, w} G) n B)) =
    (invariantsFunctor.{g, max g w} (G := G)).map
      (eqToHom (Monad.monadPow_succ_obj_eq (coindMonad.{g, w} G) n A)) ≫
      (invariantsFunctor.{g, max g w} (G := G)).map
        ((coindMonad.{g, w} G).map ((Monad.monadPow (coindMonad.{g, w} G) n).map f)) := by
  let F := invariantsFunctor.{g, max g w} (G := G)
  let T := coindMonad.{g, w} G
  exact (F.map_comp _ _).symm.trans
    ((congrArg (fun a => F.map a) (Monad.monadPow_succ_obj_eq_naturality T n f)).trans
      (F.map_comp _ _))

/-- All positive monad-power invariant terms retain the actual original exact coefficient
sequence. -/
theorem coindPowerInvariants_shortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, max g w} G))
    (hS : (S.map (forget.{g, max g w} G)).ShortExact) (n : ℕ) :
    letI := coindMonadPower_preservesZero.{g, w} G (n + 1)
    ((S.map (Monad.monadPow (coindMonad.{g, w} G) (n + 1))).map
        (invariantsFunctor.{g, max g w} (G := G))).ShortExact := by
  let := coindMonadPower_preservesZero.{g, w} G (n + 1)
  let T := coindMonad.{g, w} G
  let : T.toFunctor.PreservesZeroMorphisms := by
    change (coind.{g, w} (G := G)).PreservesZeroMorphisms
    infer_instance
  let P := S.map (Monad.monadPow T n)
  let U := (S.map (Monad.monadPow T (n + 1))).map (invariantsFunctor.{g, max g w} (G := G))
  let V := (P.map T.toFunctor).map (invariantsFunctor.{g, max g w} (G := G))
  let q₁ := (invariantsFunctor.{g, max g w} (G := G)).mapIso
      (eqToIso (Monad.monadPow_succ_obj_eq T n S.X₁))
  let q₂ := (invariantsFunctor.{g, max g w} (G := G)).mapIso
      (eqToIso (Monad.monadPow_succ_obj_eq T n S.X₂))
  let q₃ := (invariantsFunctor.{g, max g w} (G := G)).mapIso
      (eqToIso (Monad.monadPow_succ_obj_eq T n S.X₃))
  let e : U ≅ V := ShortComplex.isoMk q₁ q₂ q₃
    (by
      exact (coindPowerSucc_invariants_naturality.{g, w} G n S.f).symm)
    (by
      exact (coindPowerSucc_invariants_naturality.{g, w} G n S.g).symm)
  exact ShortComplex.shortExact_of_iso e.symm
    (coindInvariants_shortExact.{g, w} G P (coindPower_forget_shortExact.{g, w} G S hS n))

end CategoryTheory.DiscreteAbelianAction
