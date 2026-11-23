/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: ported tensor-instance alphabet padding and generalized its value theorem
to explicit finite source and target alphabets.
-/
module

public import MathlibExt.Combinatorics.TensorNetwork.Presentation

/-! # Tensor-instance alphabet padding

This module renames the active edge alphabet of a tensor instance, returning zero when an active
target label is outside the named subset. The diagonal coordinate is always replaced by the source
default before the original tensor is evaluated.

Adapted from `eth/proof/networks/Groundwork/Net/Defs.lean` and
`eth/proof/networks/Groundwork/Net/Net.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace TensorNetwork

open Finset

variable {J A A' : Type*}

namespace Instance

/-- Rename the active edge alphabet of an instance through `dec`, returning zero when any
off-diagonal target label is outside `D`. The diagonal coordinate is replaced by `sourceDefault`. -/
def pad [Fintype J] [DecidableEq J] [DecidableEq A'] (R : Instance J A)
    (sourceDefault : A) (D : Finset A') (dec : A' → A) : Instance J A' :=
  fun v θ =>
    if ∀ w, w ≠ v → θ w ∈ D then
      R v (fun w => if w = v then sourceDefault else dec (θ w))
    else 0

/-- Factoring an instance and converting it back through constant edge names gives its padded
version. The decoder must send every admitted target name into the explicit source alphabet. -/
theorem toInstance_toFactored_eq_pad [Fintype J] [LinearOrder J]
    [DecidableEq A] [DecidableEq A'] (R : Instance J A) (sourceLabels : Finset A)
    (sourceDefault : A) (D : Finset A') (dec : A' → A)
    (hdec : Set.MapsTo dec D sourceLabels) :
    (R.toFactored sourceLabels sourceDefault).toInstance (fun _ _ => D) (fun _ _ => dec) =
      R.pad sourceDefault D dec := by
  funext v θ
  unfold Factored.toInstance pad toFactored
  simp only
  split_ifs with hall
  · rw [Finset.sum_eq_single (fun w => if w = v then sourceDefault else dec (θ w))]
    · rw [Finset.prod_eq_one, mul_one]
      intro b hb
      have hb' : b ≠ v := by simpa using hb
      simp [hall b hb', hb']
    · intro z hz hne
      have hz' := (Fintype.mem_piFinsetOn
        (fun w : J => w ≠ v) (fun _ => sourceLabels) sourceDefault z).mp hz
      obtain ⟨b, hb⟩ : ∃ b, z b ≠ (if b = v then sourceDefault else dec (θ b)) := by
        by_contra hcon
        exact hne (funext fun b => by_contra fun hb => hcon ⟨b, hb⟩)
      have hbv : b ≠ v := by
        rintro rfl
        exact hb (by simpa using (hz' b).2 (by simp))
      rw [Finset.prod_eq_zero (i := b) (by simp [hbv]), mul_zero]
      simp only [hbv, ite_false] at hb
      simp [hall b hbv, hb]
    · intro hn
      exfalso
      apply hn
      rw [Fintype.mem_piFinsetOn]
      intro w
      constructor
      · intro hwv
        simpa [hwv] using hdec (hall w hwv)
      · intro hwv
        have hw : w = v := not_ne_iff.mp hwv
        subst w
        simp
  · obtain ⟨w, hw, hwD⟩ : ∃ w, w ≠ v ∧ θ w ∉ D := by
      by_contra hcon
      exact hall fun w hw => by_contra fun hD => hcon ⟨w, hw, hD⟩
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [Finset.prod_eq_zero (i := w) (by simp [hw]), mul_zero]
    simp [hwD]

/-- The source conversion theorem with the full finite source alphabet. -/
theorem toInstance_toFactored_univ_eq_pad [Fintype J] [LinearOrder J] [Fintype A]
    [DecidableEq A] [DecidableEq A'] (R : Instance J A) (sourceDefault : A)
    (D : Finset A') (dec : A' → A) :
    (R.toFactored univ sourceDefault).toInstance (fun _ _ => D) (fun _ _ => dec) =
      R.pad sourceDefault D dec := by
  exact R.toInstance_toFactored_eq_pad univ sourceDefault D dec (by simp)

/-- Padding through a bijective renaming of an explicit source alphabet preserves instance value. -/
theorem value_pad [Fintype J] [LinearOrder J] [DecidableEq A] [DecidableEq A']
    (R : Instance J A) (sourceLabels : Finset A) (sourceDefault : A)
    (targetLabels : Finset A') (targetDefault : A') (D : Finset A') (dec : A' → A)
    (hD : D ⊆ targetLabels) (hdec : Set.BijOn dec D sourceLabels) :
    (R.pad sourceDefault D dec).value targetLabels targetDefault =
      R.value sourceLabels sourceDefault := by
  rw [← R.toInstance_toFactored_eq_pad sourceLabels sourceDefault D dec hdec.mapsTo]
  rw [Factored.value_toInstance (R.toFactored sourceLabels sourceDefault) targetLabels
    targetDefault (fun _ _ => D) (fun _ _ => dec)
    (by intro _ _ _; exact hD)
    (by intro _ _ _; simpa [toFactored] using hdec)]
  exact (R.value_toFactored sourceLabels sourceDefault).symm

end Instance

end TensorNetwork
