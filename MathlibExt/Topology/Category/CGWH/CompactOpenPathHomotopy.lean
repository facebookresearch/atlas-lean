/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.CGWH.CompactOpenParameterEvaluation
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Category.CompHaus.Basic

/-!
# Evaluating one whole compact-open path homotopy

A path homotopy in the actual compact-open mapping space has a compact
square parameter. The generated mapping homeomorphism and compact-parameter
evaluation give a jointly continuous map on that square times the entire
active source. All four square faces are the original path-homotopy faces.
No local compactness of the active source or pointwise filling is assumed.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Topology

universe u

namespace CGWH

variable {A B : CGWH.{u, u}} [T2Space A]
  {a₀ a₁ : C(A, B)} {p q : Path a₀ a₁}

private def compactOpenPathHomotopyRecipe (H : p.Homotopy q) :
    C((unitInterval × unitInterval) × A, B) := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  let Kc : CompHaus.{u} := CompHaus.of (ULift.{u} (unitInterval × unitInterval))
  letI : IsGeneratedBy P Kc := by
    change IsGeneratedBy P (P Kc)
    infer_instance
  letI : UCompactlyGeneratedSpace.{u} Kc :=
    (isGeneratedBy_compactHausProbes_iff (Y := Kc)).mp inferInstance
  let K : CGWH.{u, u} := CGWH.of Kc
  let e : K ≃ₜ (unitInterval × unitInterval) := Homeomorph.ulift
  let f : C(K, C(A, B)) :=
    H.toHomotopy.toContinuousMap.comp (e : C(K, unitInterval × unitInterval))
  exact (compactOpenParameterEvaluationMap f).comp
    ((e.symm : C(unitInterval × unitInterval, K)).prodMap (ContinuousMap.id A))

private theorem compactOpenPathHomotopyRecipe_apply
    (H : p.Homotopy q) (t s : unitInterval) (a : A) :
    compactOpenPathHomotopyRecipe H ((t, s), a) = H (t, s) a := by
  let P := CompactlyGenerated.compactHausProbes.{u}
  let Kc : CompHaus.{u} := CompHaus.of (ULift.{u} (unitInterval × unitInterval))
  letI : IsGeneratedBy P Kc := by
    change IsGeneratedBy P (P Kc)
    infer_instance
  letI : UCompactlyGeneratedSpace.{u} Kc :=
    (isGeneratedBy_compactHausProbes_iff (Y := Kc)).mp inferInstance
  let K : CGWH.{u, u} := CGWH.of Kc
  let e : K ≃ₜ (unitInterval × unitInterval) := Homeomorph.ulift
  let f : C(K, C(A, B)) :=
    H.toHomotopy.toContinuousMap.comp (e : C(K, unitInterval × unitInterval))
  change compactOpenParameterEvaluationMap f (e.symm (t, s), a) = H (t, s) a
  exact (compactOpenParameterEvaluationMap_apply f (e.symm (t, s)) a).trans
    (congrArg (fun z => H z a) (e.apply_symm_apply (t, s)))

/-- One actual compact-open path homotopy evaluates jointly continuously
on the complete active source. Only the compact parameter is lifted in
universe; neither the coefficient ring nor the active target is replaced. -/
public def compactOpenPathHomotopyEvaluation (H : p.Homotopy q) :
    C((unitInterval × unitInterval) × A, B) :=
  compactOpenPathHomotopyRecipe H

/-- Every original square and active-parameter value is preserved. -/
public theorem compactOpenPathHomotopyEvaluation_apply
    (H : p.Homotopy q) (t s : unitInterval) (a : A) :
    compactOpenPathHomotopyEvaluation H ((t, s), a) = H (t, s) a := by
  unfold compactOpenPathHomotopyEvaluation
  exact compactOpenPathHomotopyRecipe_apply H t s a

/-- The initial homotopy face is the whole original first path family. -/
public theorem compactOpenPathHomotopyEvaluation_zero
    (H : p.Homotopy q) (s : unitInterval) (a : A) :
    compactOpenPathHomotopyEvaluation H ((0, s), a) = p s a := by
  rw [compactOpenPathHomotopyEvaluation_apply]
  exact congrArg (fun f : C(A, B) => f a) (H.toHomotopy.map_zero_left s)

/-- The terminal homotopy face is the whole original second path family. -/
public theorem compactOpenPathHomotopyEvaluation_one
    (H : p.Homotopy q) (s : unitInterval) (a : A) :
    compactOpenPathHomotopyEvaluation H ((1, s), a) = q s a := by
  rw [compactOpenPathHomotopyEvaluation_apply]
  exact congrArg (fun f : C(A, B) => f a) (H.toHomotopy.map_one_left s)

/-- The original source face is fixed for every time and every active point. -/
public theorem compactOpenPathHomotopyEvaluation_source
    (H : p.Homotopy q) (t : unitInterval) (a : A) :
    compactOpenPathHomotopyEvaluation H ((t, 0), a) = a₀ a := by
  rw [compactOpenPathHomotopyEvaluation_apply]
  exact congrArg (fun f : C(A, B) => f a) (Path.Homotopy.source H t)

/-- The original target face is fixed for every time and every active point. -/
public theorem compactOpenPathHomotopyEvaluation_target
    (H : p.Homotopy q) (t : unitInterval) (a : A) :
    compactOpenPathHomotopyEvaluation H ((t, 1), a) = a₁ a := by
  rw [compactOpenPathHomotopyEvaluation_apply]
  exact congrArg (fun f : C(A, B) => f a) (Path.Homotopy.target H t)

private def compactOpenPathEvaluationRecipe (p : Path a₀ a₁) : C(unitInterval × A, B) :=
  (compactOpenPathHomotopyEvaluation (Path.Homotopy.refl p)).comp
    (((ContinuousMap.const (unitInterval × A) (0 : unitInterval)).prodMk
      (ContinuousMap.fst : C(unitInterval × A, unitInterval))).prodMk
        (ContinuousMap.snd : C(unitInterval × A, A)))

/-- One actual compact-open path evaluates jointly on the ENTIRE native
active source. This uses the already derived compact-square evaluation
on its reflexive path homotopy, with no local-compactness input on A. -/
public def compactOpenPathEvaluation (p : Path a₀ a₁) : C(unitInterval × A, B) :=
  compactOpenPathEvaluationRecipe p

private theorem compactOpenPathEvaluation_apply_computed
    (p : Path a₀ a₁) (t : unitInterval) (a : A) :
    compactOpenPathEvaluation p (t, a) = p t a := by
  unfold compactOpenPathEvaluation compactOpenPathEvaluationRecipe
  change compactOpenPathHomotopyEvaluation (Path.Homotopy.refl p) ((0, t), a) = p t a
  exact compactOpenPathHomotopyEvaluation_zero (Path.Homotopy.refl p) t a

/-- Every time and every original active point is unchanged by evaluation. -/
public theorem compactOpenPathEvaluation_apply
    (p : Path a₀ a₁) (t : unitInterval) (a : A) :
    compactOpenPathEvaluation p (t, a) = p t a :=
  compactOpenPathEvaluation_apply_computed p t a

/-- The whole initial endpoint is the ORIGINAL first mapping-space point. -/
public theorem compactOpenPathEvaluation_zero (p : Path a₀ a₁) (a : A) :
    compactOpenPathEvaluation p (0, a) = a₀ a :=
  (compactOpenPathEvaluation_apply p 0 a).trans (congrArg (fun f : C(A, B) => f a) p.source)

/-- The whole terminal endpoint is the ORIGINAL second mapping-space point. -/
public theorem compactOpenPathEvaluation_one (p : Path a₀ a₁) (a : A) :
    compactOpenPathEvaluation p (1, a) = a₁ a :=
  (compactOpenPathEvaluation_apply p 1 a).trans (congrArg (fun f : C(A, B) => f a) p.target)

/-- One jointly continuous square with its FOUR complete original faces
gives a homotopy of the ORIGINAL whole mapping-space loop to the constant
path. No separate pointwise nullhomotopies are assembled here. -/
public theorem mappingSpaceLoop_homotopic_refl_of_square
    {Source Target : Type*} [TopologicalSpace Source] [TopologicalSpace Target]
    {c : C(Source, Target)} (p : Path c c)
    (K : C((unitInterval × unitInterval) × Source, Target))
    (h₀ : ∀ s a, K ((0, s), a) = p s a)
    (h₁ : ∀ s a, K ((1, s), a) = c a)
    (hsource : ∀ t a, K ((t, 0), a) = c a)
    (htarget : ∀ t a, K ((t, 1), a) = c a) : p.Homotopic (Path.refl c) := by
  refine ⟨{ toFun := K.curry
            continuous_toFun := K.curry.continuous
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }⟩
  · intro s
    apply ContinuousMap.ext
    intro a
    exact h₀ s a
  · intro s
    apply ContinuousMap.ext
    intro a
    exact h₁ s a
  · intro t s hs
    apply ContinuousMap.ext
    intro a
    rcases hs with rfl | hs
    · exact (hsource t a).trans (congrArg (fun f : C(Source, Target) => f a) p.source).symm
    · rw [Set.mem_singleton_iff] at hs
      subst s
      exact (htarget t a).trans (congrArg (fun f : C(Source, Target) => f a) p.target).symm

end CGWH

end
