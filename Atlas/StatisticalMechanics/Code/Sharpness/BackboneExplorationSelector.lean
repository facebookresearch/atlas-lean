/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























import Mathlib

open Finset

set_option linter.unusedSectionVars false

namespace StatMech.Sharpness







structure shb_DynamicEdgeExploration (D E : Type*) where
  edgeOrder : D → List E
  edgeOrder_nodup : ∀ D, (edgeOrder D).Nodup
  advance : D → E → D

namespace shb_DynamicEdgeExploration

variable {D E : Type*} [DecidableEq E]


def firstAdmissible (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) : Option E :=
  (X.edgeOrder d).find? (admissible d)



theorem firstAdmissible_mem (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (e : E)
    (h : X.firstAdmissible admissible d = some e) :
    e ∈ X.edgeOrder d :=
  List.mem_of_find?_eq_some h


theorem firstAdmissible_isAdmissible (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (e : E)
    (h : X.firstAdmissible admissible d = some e) :
    admissible d e = true :=
  List.find?_some h



def determinedAt (X : shb_DynamicEdgeExploration D E) (d : D) (e : E) : List E :=
  (X.edgeOrder d).takeWhile (fun f => f ≠ e) ++ [e]


def residual (X : shb_DynamicEdgeExploration D E) : D → List E → D
  | d, [] => d
  | d, e :: es => residual X (X.advance d e) es


def determinedTrace (X : shb_DynamicEdgeExploration D E) : D → List E → List E
  | _, [] => []
  | d, e :: es => X.determinedAt d e ++ X.determinedTrace (X.advance d e) es



def Selects (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) : D → List E → Prop
  | _, [] => True
  | d, e :: es =>
      X.firstAdmissible admissible d = some e ∧
        X.Selects admissible (X.advance d e) es

@[simp] theorem residual_nil (X : shb_DynamicEdgeExploration D E) (d : D) :
    X.residual d [] = d := rfl

@[simp] theorem residual_cons (X : shb_DynamicEdgeExploration D E)
    (d : D) (e : E) (es : List E) :
    X.residual d (e :: es) = X.residual (X.advance d e) es := rfl


theorem residual_append (X : shb_DynamicEdgeExploration D E)
    (d : D) (p q : List E) :
    X.residual d (p ++ q) = X.residual (X.residual d p) q := by
  induction p generalizing d with
  | nil => rfl
  | cons e p ih =>
      simp only [List.cons_append, residual_cons]
      exact ih (X.advance d e)

@[simp] theorem determinedTrace_nil (X : shb_DynamicEdgeExploration D E) (d : D) :
    X.determinedTrace d [] = [] := rfl

@[simp] theorem determinedTrace_cons (X : shb_DynamicEdgeExploration D E)
    (d : D) (e : E) (es : List E) :
    X.determinedTrace d (e :: es) =
      X.determinedAt d e ++ X.determinedTrace (X.advance d e) es := rfl



theorem determinedTrace_append (X : shb_DynamicEdgeExploration D E)
    (d : D) (p q : List E) :
    X.determinedTrace d (p ++ q) =
      X.determinedTrace d p ++ X.determinedTrace (X.residual d p) q := by
  induction p generalizing d with
  | nil => rfl
  | cons e p ih =>
      simp only [List.cons_append, determinedTrace_cons, residual_cons]
      rw [ih]
      exact (List.append_assoc _ _ _).symm

@[simp] theorem selects_nil (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) :
    X.Selects admissible d [] := trivial

@[simp] theorem selects_cons (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (e : E) (es : List E) :
    X.Selects admissible d (e :: es) ↔
      X.firstAdmissible admissible d = some e ∧
        X.Selects admissible (X.advance d e) es := Iff.rfl




theorem selects_append_iff (X : shb_DynamicEdgeExploration D E)
    (admissible : D → E → Bool) (d : D) (p q : List E) :
    X.Selects admissible d (p ++ q) ↔
      X.Selects admissible d p ∧
        X.Selects admissible (X.residual d p) q := by
  induction p generalizing d with
  | nil => simp
  | cons e p ih =>
      simp only [List.cons_append, selects_cons, residual_cons, ih]
      tauto

end shb_DynamicEdgeExploration










structure shb_ExplorationKernel (D E : Type*) [Preorder D] [DecidableEq E] where
  exploration : shb_DynamicEdgeExploration D E
  amplitude : D → E → ℝ
  amplitude_nonneg : ∀ d e, 0 ≤ amplitude d e
  amplitude_antitone : ∀ {small large}, small ≤ large → ∀ e,
    amplitude large e ≤ amplitude small e
  advance_mono : ∀ {small large}, small ≤ large → ∀ e,
    exploration.advance small e ≤ exploration.advance large e

namespace shb_ExplorationKernel

variable {D E : Type*} [Preorder D] [DecidableEq E]


def weight (K : shb_ExplorationKernel D E) : D → List E → ℝ
  | _, [] => 1
  | d, e :: es => K.amplitude d e * K.weight (K.exploration.advance d e) es

@[simp] theorem weight_nil (K : shb_ExplorationKernel D E) (d : D) :
    K.weight d [] = 1 := rfl

@[simp] theorem weight_cons (K : shb_ExplorationKernel D E)
    (d : D) (e : E) (es : List E) :
    K.weight d (e :: es) =
      K.amplitude d e * K.weight (K.exploration.advance d e) es := rfl


theorem weight_nonneg (K : shb_ExplorationKernel D E) (d : D) (p : List E) :
    0 ≤ K.weight d p := by
  induction p generalizing d with
  | nil => exact zero_le_one
  | cons e p ih =>
      exact mul_nonneg (K.amplitude_nonneg d e)
        (ih (K.exploration.advance d e))



theorem weight_append (K : shb_ExplorationKernel D E)
    (d : D) (p q : List E) :
    K.weight d (p ++ q) =
      K.weight d p * K.weight (K.exploration.residual d p) q := by
  induction p generalizing d with
  | nil => simp
  | cons e p ih =>
      simp only [List.cons_append, weight_cons,
        shb_DynamicEdgeExploration.residual_cons, ih]
      ring


theorem residual_mono (K : shb_ExplorationKernel D E)
    {small large : D} (h : small ≤ large) (p : List E) :
    K.exploration.residual small p ≤ K.exploration.residual large p := by
  induction p generalizing small large with
  | nil => exact h
  | cons e p ih =>
      exact ih (K.advance_mono h e)



theorem weight_antitone (K : shb_ExplorationKernel D E)
    {small large : D} (h : small ≤ large) (p : List E) :
    K.weight large p ≤ K.weight small p := by
  induction p generalizing small large with
  | nil => exact le_rfl
  | cons e p ih =>
      exact mul_le_mul (K.amplitude_antitone h e)
        (ih (K.advance_mono h e))
        (K.weight_nonneg _ _) (K.amplitude_nonneg _ _)

end shb_ExplorationKernel







structure shb_ExplorationRhoRealization
    (D E : Type*) [Preorder D] [DecidableEq E] where
  kernel : shb_ExplorationKernel D E
  rho : D → List E → ℝ
  rho_eq_weight : ∀ d p, rho d p = kernel.weight d p

namespace shb_ExplorationRhoRealization

variable {D E : Type*} [Preorder D] [DecidableEq E]


theorem P2 (R : shb_ExplorationRhoRealization D E)
    (d : D) (p q : List E) :
    R.rho d (p ++ q) =
      R.rho d p * R.rho (R.kernel.exploration.residual d p) q := by
  rw [R.rho_eq_weight, R.kernel.weight_append,
    ← R.rho_eq_weight, ← R.rho_eq_weight]



theorem P3 (R : shb_ExplorationRhoRealization D E)
    {small large : D} (h : small ≤ large) (p : List E) :
    R.rho large p ≤ R.rho small p := by
  rw [R.rho_eq_weight, R.rho_eq_weight]
  exact R.kernel.weight_antitone h p


theorem rho_nonneg (R : shb_ExplorationRhoRealization D E)
    (d : D) (p : List E) : 0 ≤ R.rho d p := by
  rw [R.rho_eq_weight]
  exact R.kernel.weight_nonneg d p

end shb_ExplorationRhoRealization

end StatMech.Sharpness
