/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Logics.Testing.Ioco

/-! # Regressions for ioco conformance -/

set_option autoImplicit false

namespace Cslib.Testing.Ioco.Tests

private abbrev Label := Action Unit Unit

private abbrev Word := List (Observable Unit Unit)

private def silent : LTS Bool Label where
  Tr s a t := match a with
    | .tau => s = false ∧ t = true
    | .input _ | .output _ => False

private theorem silent_target_quiescent : Quiescent silent true := by
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · rintro ⟨_, h, _⟩
    cases h

-- An initial silent step prevents quiescence at the source, but the empty observation reaches
-- its target. A δ observation can then be made after that silent step.
example : ¬ Quiescent silent false ∧ true ∈ after silent false [] ∧
    true ∈ after silent false [.inr none] := by
  have hτ : silent.Tr false .tau true := ⟨rfl, rfl⟩
  have hweak : silent.τSTr false true := Relation.ReflTransGen.single hτ
  refine ⟨fun h => h.2 ⟨true, hτ⟩, mem_after_nil.mpr hweak, ?_⟩
  exact .stepL (.tr hweak ⟨rfl, silent_target_quiescent⟩ .refl) (.refl _ _)

private def quietSpec : LTS Unit Label where
  Tr _ _ _ := False

private def impl : LTS Bool Label where
  Tr s a t := match a with
    | .input _ => t = true
    | .output _ => s = true ∧ t = true
    | .tau => False

private theorem impl_enabled : InputEnabled impl false :=
  fun _ _ _ => ⟨true, LTS.STr.single rfl⟩

private theorem quietSpec_quiescent : Quiescent quietSpec () := by
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · rintro ⟨_, h⟩
    exact h

private theorem impl_quiescent : Quiescent impl false := by
  constructor
  · rintro ⟨_, _, h, _⟩
    cases h
  · rintro ⟨_, h⟩
    exact h

-- No ordinary output or input occurs on a suspension trace of this specification.
private theorem only_delta (w : Word) (h : () ∈ after quietSpec () w) :
    ∀ a ∈ w, a = .inr none := by
  induction w with
  | nil => simp
  | cons a w ih =>
      change (suspension quietSpec).SMTr () (_ :: _) () at h
      cases h with
      | stepL hs htail =>
          rename_i mid
          cases mid
          have ha : a = .inr none := by
            cases a with
            | inl i =>
                cases hs with
                | tr _ h _ => exact h.elim
            | inr o =>
                cases o with
                | none => rfl
                | some o =>
                    cases hs with
                    | tr _ h _ => exact h.elim
          intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · exact ha
          · exact ih htail b hb

private theorem impl_tau_eq {s t : Bool} (h : (suspension impl).τSTr s t) : s = t := by
  induction h with
  | refl => rfl
  | tail _ h => exact h.elim

private theorem impl_delta_residual (w : Word) (hδ : ∀ a ∈ w, a = .inr none)
    {t : Bool} (ht : t ∈ after impl false w) : t = false := by
  induction w with
  | nil =>
      have hτ := (mem_after_nil (lts := impl)).mp ht
      change (suspension impl).τSTr false t at hτ
      exact (impl_tau_eq hτ).symm
  | cons a w ih =>
      have ha := hδ a (by simp)
      subst a
      change (suspension impl).SMTr false (.output none :: _) t at ht
      cases ht with
      | stepL hs htail =>
          cases hs with
          | tr hpre hstep hpost =>
              obtain rfl := impl_tau_eq hpre
              obtain ⟨rfl, _⟩ := hstep
              obtain rfl := impl_tau_eq hpost
              exact ih (fun b hb => hδ b (List.mem_cons_of_mem _ hb)) htail

-- The implementation may produce an output only after the input that the specification omits.
example : Conforms impl false quietSpec () := by
  refine ⟨impl_enabled, ?_⟩
  intro w hw o ho
  obtain ⟨s, hs⟩ := hw
  cases s
  have hδ := only_delta w hs
  obtain ⟨t, ht, houtput⟩ := ho
  obtain rfl := impl_delta_residual w hδ ht
  cases o with
  | none => exact ⟨(), hs, quietSpec_quiescent⟩
  | some o =>
      obtain ⟨_, h, _⟩ := houtput
      cases h

-- This unspecified trace really does expose the implementation's extra output.
example : some () ∈ out impl (after impl false [.inl ()]) ∧
    [.inl ()] ∉ suspensionTraces quietSpec () := by
  constructor
  · exact ⟨true, .stepL (.single rfl) (.refl _ _), true, rfl, rfl⟩
  · rintro ⟨s, hs⟩
    cases s
    have h := only_delta [.inl ()] hs (.inl ()) (by simp)
    cases h

-- Quiescence is not an allowed initial output of a specification that must output.
private def activeSpec : LTS Unit Label where
  Tr _ a _ := match a with
    | .output _ => True
    | .input _ | .tau => False

example : ¬ Conforms impl false activeSpec () := by
  intro h
  have htrace : [] ∈ suspensionTraces activeSpec () := ⟨(), LTS.SMTr.refl _ _⟩
  have hnone : none ∈ out impl (after impl false []) :=
    ⟨false, LTS.SMTr.refl _ _, impl_quiescent⟩
  obtain ⟨s, _, hq⟩ := h.2 [] htrace hnone
  exact hq.1 ⟨(), s, trivial⟩

private def gatedInput : LTS (Fin 3) Label where
  Tr s a t := match a with
    | .tau => s = 0 ∧ t = 1
    | .input _ => s = 1 ∧ t = 1
    | .output _ => False

private theorem gated_reachable {s t : Fin 3} {labels : List Label}
    (h : gatedInput.MTr s labels t) (hs : s = 0 ∨ s = 1) : t = 0 ∨ t = 1 := by
  induction h with
  | refl => exact hs
  | @stepL _ a _ _ _ hstep _ ih =>
      apply ih
      right
      cases a with
      | input _ => exact hstep.2
      | output _ => exact hstep.elim
      | tau => exact hstep.2

-- Weak input-enabledness allows the silent lead-in and ignores the unreachable state 2.
example : InputEnabled gatedInput 0 := by
  intro s h _
  obtain ⟨_, htrace⟩ := h
  rcases gated_reachable htrace (Or.inl rfl) with rfl | rfl
  · have hτ : gatedInput.τSTr 0 1 := Relation.ReflTransGen.single ⟨rfl, rfl⟩
    exact ⟨1, .tr hτ ⟨rfl, rfl⟩ .refl⟩
  · exact ⟨1, .single ⟨rfl, rfl⟩⟩

end Cslib.Testing.Ioco.Tests
