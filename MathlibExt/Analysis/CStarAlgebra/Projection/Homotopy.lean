/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Star.Projection
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Path

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

/-!
# Homotopy of C-star projections

Projections at distance less than one in a complex C-star algebra are
Murray--von Neumann equivalent.  Consequently, the endpoints of a
norm-continuous path of projections are Murray--von Neumann equivalent.
-/

@[expose] public section

open Set
open scoped CStarAlgebra

namespace StarProjection

noncomputable section

universe u

/-- Projections at norm distance less than one in a complex nonunital C-star
algebra are Murray--von Neumann equivalent. -/
theorem murrayVonNeumannEquivalent_of_norm_sub_lt_one
    {A : Type u} [NonUnitalCStarAlgebra A]
    {p q : StarProjection A}
    (h : ‖(p : A) - (q : A)‖ < 1) :
    MurrayVonNeumannEquivalent p q := by
  let _ : PartialOrder A := CStarAlgebra.spectralOrder A
  let _ : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let P : Unitization ℂ A := Unitization.inr (p : A)
  let Q : Unitization ℂ A := Unitization.inr (q : A)
  let D : Unitization ℂ A := P - Q
  let W : Unitization ℂ A := Q * P + (1 - Q) * (1 - P)
  let a : Unitization ℂ A := star W * W
  -- Record the projection identities inside the unitization.
  have hPstar : star P = P := by
    simpa only [P, Unitization.inr_star] using
      congrArg (Unitization.inr (R := ℂ) : A → Unitization ℂ A)
        p.property.isSelfAdjoint.star_eq
  have hQstar : star Q = Q := by
    simpa only [Q, Unitization.inr_star] using
      congrArg (Unitization.inr (R := ℂ) : A → Unitization ℂ A)
        q.property.isSelfAdjoint.star_eq
  have hPid : P * P = P := by
    simpa [P] using congrArg (Unitization.inr : A → Unitization ℂ A)
      p.property.isIdempotentElem.eq
  have hQid : Q * Q = Q := by
    simpa [Q] using congrArg (Unitization.inr : A → Unitization ℂ A)
      q.property.isIdempotentElem.eq
  have hPPQ : P * (P * Q) = P * Q := by
    rw [← mul_assoc, hPid]
  have hQQP : Q * (Q * P) = Q * P := by
    rw [← mul_assoc, hQid]
  -- Compute both adjoint products of the raw intertwiner.
  have hWP : W * P = Q * W := by
    dsimp [W]
    noncomm_ring [hPid, hQid, hPPQ, hQQP]
  have hstarW : star W = P * Q + (1 - P) * (1 - Q) := by
    simp [W, star_add, star_mul, hPstar, hQstar]
  have hleft : star W * W = 1 - D * D := by
    rw [hstarW]
    dsimp [W, D]
    noncomm_ring [hPid, hQid, hPPQ, hQQP]
  have hright : W * star W = 1 - D * D := by
    rw [hstarW]
    dsimp [W, D]
    noncomm_ring [hPid, hQid, hPPQ, hQQP]
  have hnormal : W * star W = star W * W :=
    hright.trans hleft.symm
  -- Invert the common positive adjoint product.
  have hD : ‖D‖ < 1 := by
    simpa [D, P, Q, ← Unitization.inr_sub, Unitization.norm_inr] using h
  have hDD : ‖D * D‖ < 1 := by
    calc
      ‖D * D‖ ≤ ‖D‖ * ‖D‖ := norm_mul_le D D
      _ < 1 := by nlinarith [norm_nonneg D]
  let aUnit : (Unitization ℂ A)ˣ := Units.oneSub (D * D) hDD
  have haUnit : IsUnit a := by
    refine ⟨aUnit, ?_⟩
    simpa [aUnit, a] using hleft.symm
  have haNonneg : 0 ≤ a := by
    dsimp [a]
    exact star_mul_self_nonneg W
  have haStrict : IsStrictlyPositive a :=
    haUnit.isStrictlyPositive haNonneg
  -- Form its inverse half-power by continuous functional calculus.
  let b : Unitization ℂ A := a ^ (-(1 / 2) : ℝ)
  have hbNonneg : 0 ≤ b := by
    dsimp [b]
    exact CFC.rpow_nonneg
  have hbStar : star b = b :=
    (IsSelfAdjoint.of_nonneg hbNonneg).star_eq
  have hbab : b * a * b = 1 := by
    dsimp [b]
    exact CFC.conjugate_rpow_neg_one_half a haStrict
  -- Move the inverse half-power through the relevant commuting elements.
  have haW : Commute a W := by
    change a * W = W * a
    dsimp [a]
    calc
      (star W * W) * W = (W * star W) * W :=
        congrArg (fun x => x * W) hnormal.symm
      _ = W * (star W * W) := by rw [mul_assoc]
  have haP : Commute a P := by
    change a * P = P * a
    dsimp [a]
    rw [hleft]
    dsimp [D]
    noncomm_ring [hPid, hQid, hPPQ, hQQP]
  -- Convert commutation with `a` into commutation with its inverse half-power.
  have commute_rpow (x : Unitization ℂ A) (hx : Commute a x) :
      Commute b x := by
    dsimp [b]
    rw [CFC.rpow_eq_cfc_real haNonneg]
    exact hx.cfc_real _
  have hbW : Commute b W := commute_rpow W haW
  have hbP : Commute b P := commute_rpow P haP
  have hbStarW : b * star W = star W * b := by
    simpa only [star_mul, hbStar] using (congrArg star hbW.eq).symm
  -- Normalize the raw intertwiner to a unitary.
  let u : Unitization ℂ A := W * b
  have huStarMul : star u * u = 1 := by
    dsimp [u]
    rw [star_mul, hbStar]
    calc
      (b * star W) * (W * b) = b * (star W * W) * b := by
        simp only [mul_assoc]
      _ = b * a * b := by rfl
      _ = 1 := hbab
  have huMulStar : u * star u = 1 := by
    dsimp [u]
    rw [star_mul, hbStar]
    calc
      (W * b) * (b * star W) = b * W * (b * star W) := by
        rw [← hbW.eq]
      _ = b * W * (star W * b) := by rw [hbStarW]
      _ = b * (W * star W) * b := by simp only [mul_assoc]
      _ = b * a * b := by rw [hright, ← hleft]
      _ = 1 := hbab
  have huP : u * P = Q * u := by
    dsimp [u]
    calc
      (W * b) * P = W * (b * P) := by simp only [mul_assoc]
      _ = W * (P * b) := by rw [hbP.eq]
      _ = (W * P) * b := by simp only [mul_assoc]
      _ = (Q * W) * b := by rw [hWP]
      _ = Q * (W * b) := by simp only [mul_assoc]
  have huConj : u * P * star u = Q := by
    calc
      u * P * star u = Q * u * star u := by rw [huP]
      _ = Q * (u * star u) := by simp only [mul_assoc]
      _ = Q := by rw [huMulStar, mul_one]
  -- Descend the zero-scalar element `uP` to the original nonunital algebra.
  let V : Unitization ℂ A := u * P
  let v : A := V.snd
  have hVinr : Unitization.inr v = V := by
    apply Unitization.ext
    · simp [v, V, P]
    · rfl
  -- The descended element is the rectangular equivalence witness.
  refine ⟨v, ?_, ?_⟩
  · have hv : Unitization.inr (star v * v) = P := by
      calc
        Unitization.inr (star v * v) =
            star (Unitization.inr v) * Unitization.inr v := by simp
        _ = star V * V := by rw [hVinr]
        _ = star (u * P) * (u * P) := by rfl
        _ = P * star u * u * P := by
          rw [star_mul, hPstar]
          simp only [mul_assoc]
        _ = P * (star u * u) * P := by simp only [mul_assoc]
        _ = P := by rw [huStarMul, mul_one, hPid]
    exact (Unitization.inr_injective hv).symm
  · have hv : Unitization.inr (v * star v) = Q := by
      calc
        Unitization.inr (v * star v) =
            Unitization.inr v * star (Unitization.inr v) := by simp
        _ = V * star V := by rw [hVinr]
        _ = (u * P) * star (u * P) := by rfl
        _ = u * P * P * star u := by
          rw [star_mul, hPstar]
          simp only [mul_assoc]
        _ = u * (P * P) * star u := by simp only [mul_assoc]
        _ = u * P * star u := by rw [hPid]
        _ = Q := huConj
    exact (Unitization.inr_injective hv).symm

/-- The endpoints of a norm-continuous path of star projections in a complex
nonunital C-star algebra are Murray--von Neumann equivalent. -/
theorem murrayVonNeumannEquivalent_of_path
    {A : Type u} [NonUnitalCStarAlgebra A]
    {p q : StarProjection A} (gamma : Path p q) :
    MurrayVonNeumannEquivalent p q := by
  let S : Set (StarProjection A) :=
    {r | MurrayVonNeumannEquivalent p r}
  have hSOpen : IsOpen S := by
    rw [Metric.isOpen_iff]
    intro r hr
    refine ⟨1, zero_lt_one, ?_⟩
    intro s hs
    have hsr : ‖(s : A) - (r : A)‖ < 1 := by
      simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hs
    exact murrayVonNeumannEquivalent_trans hr
      (murrayVonNeumannEquivalent_symm
        (murrayVonNeumannEquivalent_of_norm_sub_lt_one hsr))
  have hSComplOpen : IsOpen Sᶜ := by
    rw [Metric.isOpen_iff]
    intro r hr
    refine ⟨1, zero_lt_one, ?_⟩
    intro s hs
    have hsr : ‖(s : A) - (r : A)‖ < 1 := by
      simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using hs
    intro hps
    exact hr (murrayVonNeumannEquivalent_trans hps
      (murrayVonNeumannEquivalent_of_norm_sub_lt_one hsr))
  have hSClosed : IsClosed S := by
    simpa only [compl_compl] using hSComplOpen.isClosed_compl
  have hSClopen : IsClopen S := ⟨hSClosed, hSOpen⟩
  have hRangeConnected : IsConnected (Set.range gamma) :=
    isConnected_range gamma.continuous
  have hMeet : (Set.range gamma ∩ S).Nonempty := by
    refine ⟨p, ⟨?_, murrayVonNeumannEquivalent_refl p⟩⟩
    exact ⟨0, gamma.source⟩
  have hRange : Set.range gamma ⊆ S :=
    hRangeConnected.isPreconnected.subset_isClopen hSClopen hMeet
  exact hRange ⟨1, gamma.target⟩

end

end StarProjection
