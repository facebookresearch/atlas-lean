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

/-!
# Exactness of coinduction powers and their fixed points

Let G be a compact, totally disconnected topological group in universe g, with discrete
continuous abelian coefficients in W=max(g,w). The coinduction monad T preserves additive
morphism operations. If a coefficient row is short exact after forgetting the action, every
power T^n preserves its short exactness, both on the underlying abelian groups and in the action
category.

Evaluation at 1 identifies (TA)^G with the underlying coefficient group A. Consequently,
applying fixed points after any positive power T^{n+1} preserves these short exact coefficient
rows. The natural reassociation T^{n+1}A≅T(T^n A) relates the power functors and the evaluation
comparisons; no exactness of the fixed-point functor on arbitrary actions is required.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
universe g w
namespace CategoryTheory.DiscreteAbelianAction
variable (G : Type g) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Let G be a group with a topology in universe g and let discrete continuous abelian actions have
coefficient universe W=max(g,w). The fixed-point functor F:A↦A^G is additive: for parallel
equivariant additive maps f,h:A→B, F(f+h)=F(f)+F(h). Each map is the restriction of the
coefficient map to fixed elements. -/
instance invariants_additive : (invariantsFunctor.{g, max g w} (G := G)).Additive where
  map_add := by
    intro A B f h
    ext c
    rfl

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). Write U for the functor to abelian groups, T
for diagonal coinduction, and F for the fixed-point functor A↦A^G. For A, the group isomorphism
e_A:F(TA)≅UA evaluates an invariant continuous function at the identity. A fixed function
satisfies c(g)=g•c(1), so its value at 1 determines the entire function and every a∈A gives the
invariant function g↦g•a. -/
def coindInvariantsIso (A : DiscreteAbelianAction.{g, max g w} G) :
    invariantsFunctor.obj (coind.{g, w}.obj A) ≅ (forget.{g, max g w} G).obj A := by
  let X := toTopRep.obj A
  let hX := toTopRep_action_isContinuous A
  let e := ContinuousCohomology.coindInvariantModuleIso.{0, g, w} X hX
  let Q := forget₂ (TopModuleCat.{max g w} ℤ) (ModuleCat.{max g w} ℤ) ⋙
    forget₂ (ModuleCat.{max g w} ℤ) AddCommGrpCat.{max g w}
  exact (Q.mapIso ((TopRep.invariantsFunctor ℤ G).mapIso (coindToTopRepIso.{g, w} G A))) ≪≫
    (forget₂ (ModuleCat.{max g w} ℤ) AddCommGrpCat.{max g w}).mapIso e

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). Write U for the functor to abelian groups, T
for diagonal coinduction, and F for the fixed-point functor A↦A^G. For c∈F(TA), the forward
isomorphism e_A:F(TA)≅UA satisfies e_A.hom(c)=c(1). The element c is an invariant continuous
function G→A for the diagonal coinduction action. -/
theorem coindInvariantsIso_hom_apply (A : DiscreteAbelianAction.{g, max g w} G)
    (c : invariantsFunctor.obj (coind.{g, w}.obj A)) :
    (coindInvariantsIso.{g, w} G A).hom c = coindFunction.{g, w} A c.val 1 := rfl

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). Write U for the functor to abelian groups, T
for diagonal coinduction, and F for the fixed-point functor A↦A^G. Let S=(A --a→ B --b→ C) be a
short complex of actions whose underlying abelian-group row U(S) is short exact. Then F(TS) is
short exact. The three evaluation isomorphisms e_A,e_B,e_C:F(T(-))≅U(-) form an isomorphism from
F(TS) to U(S), preserving both arrows. -/
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

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). Write U for the functor to abelian groups, T
for diagonal coinduction, and F for the fixed-point functor A↦A^G. For every n≥0, the
endofunctor T^n is additive. Thus T^n(f+h)=T^n(f)+T^n(h) for parallel coefficient morphisms,
including n=0 where T^0 is the identity functor. -/
instance coindMonadPower_additive (n : ℕ) : (Monad.monadPow (coindMonad.{g, w} G) n).Additive := by
  induction n with
  | zero => change (𝟭 _).Additive; infer_instance
  | succ n ih =>
    change (coind.{g, w} ⋙ Monad.monadPow (coindMonad.{g, w} G) n).Additive
    infer_instance

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). Write U for the functor to abelian groups, T
for diagonal coinduction, and F for the fixed-point functor A↦A^G. For every n≥0 and every pair
of coefficient actions A,B, the power functor T^n sends the zero morphism A→B to the zero
morphism T^n A→T^n B. This follows from additivity of T^n. -/
instance coindMonadPower_preservesZero (n : ℕ) :
    (Monad.monadPow (coindMonad.{g, w} G) n).PreservesZeroMorphisms := by
  let : (Monad.monadPow (coindMonad.{g, w} G) n).Additive :=
    coindMonadPower_additive.{g, w} G n
  infer_instance

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). Write U for the functor to abelian groups, T
for diagonal coinduction, and F for the fixed-point functor A↦A^G. If S is a short complex of
actions and U(S) is short exact in abelian groups, then U(T^n S) is short exact for every n≥0.
Its arrows are U(T^n a) and U(T^n b) on the same n-fold coinduced coefficient objects. -/
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

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). Write U for the functor to abelian groups, T
for diagonal coinduction, and F for the fixed-point functor A↦A^G. For a short complex S=(A --a→
B --b→ C) with U(S) short exact, the row T^n A --T^n a→ T^n B --T^n b→ T^n C is short exact in
discrete continuous actions for every n≥0. Underlying short exactness supplies the kernel,
cokernel, monicity, and epicity properties. -/
theorem coindPower_shortExact
    (S : ShortComplex (DiscreteAbelianAction.{g, max g w} G))
    (hS : (S.map (forget.{g, max g w} G)).ShortExact) (n : ℕ) :
    (S.map (Monad.monadPow (coindMonad.{g, w} G) n)).ShortExact :=
  shortExact_of_forget_shortExact.{g, max g w} (G := G) _
    (coindPower_forget_shortExact.{g, w} G S hS n)

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). Write U for the functor to abelian groups, T
for diagonal coinduction, and F for the fixed-point functor A↦A^G. For n≥0, let
α_A^n:T^{n+1}A≅T(T^n A) be the canonical power reassociation. For an action morphism f:A→B,
F(T^{n+1}f)≫F((α_B^n).hom)=F((α_A^n).hom)≫F(T(T^n f)). Both paths are maps F(T^{n+1}A)→F(T(T^n
B)). -/
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

/-- Let G be a compact, totally disconnected topological group in universe g and let discrete
continuous abelian coefficients lie in W=max(g,w). Write U for the functor to abelian groups, T
for diagonal coinduction, and F for the fixed-point functor A↦A^G. For a short complex S of
actions with U(S) short exact and every n≥0, the abelian-group row F(T^{n+1}S) is short exact.
Reassociation identifies it with F(T(T^n S)), and identity evaluation identifies the latter row
with the short exact underlying row U(T^n S). The exponent is positive. -/
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
