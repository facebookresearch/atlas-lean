/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Ising.LebowitzPfisterBridgeCalculus

open Finset
open scoped BigOperators

namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]


def ghsiCrossExp2
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf₁ hf₂ : V -> Real)
    (F : ConfigSpace V -> ConfigSpace V -> Real) : Real :=
  (∑ a : ConfigSpace V, ∑ b : ConfigSpace V,
      wJ G.edgeFinset J hf₁ a * wJ G.edgeFinset J hf₂ b * F a b) /
    (ZJ G.edgeFinset J hf₁ * ZJ G.edgeFinset J hf₂)


def replicaCrossBridgeMoment
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf₁ hf₂ : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiCrossExp2 G J hf₁ hf₂ (fun a b =>
    Real.exp (r * replicaBridgeInteraction sites a b))


def replicaCrossBridgeMean
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf₁ hf₂ : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiCrossExp2 G J hf₁ hf₂ (fun a b =>
    replicaBridgeInteraction sites a b *
      Real.exp (r * replicaBridgeInteraction sites a b)) /
    replicaCrossBridgeMoment G J hf₁ hf₂ sites r


def replicaCrossBridgeVariance
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf₁ hf₂ : V -> Real) (sites : I -> V)
    (r : Real) : Real :=
  ghsiCrossExp2 G J hf₁ hf₂ (fun a b =>
      replicaBridgeInteraction sites a b ^ 2 *
        Real.exp (r * replicaBridgeInteraction sites a b)) /
      replicaCrossBridgeMoment G J hf₁ hf₂ sites r -
    replicaCrossBridgeMean G J hf₁ hf₂ sites r ^ 2

theorem ghsiCrossExp2_same
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (F : ConfigSpace V -> ConfigSpace V -> Real) :
    ghsiCrossExp2 G J hf hf F = ghsiExp2 G J hf F := by
  unfold ghsiCrossExp2 ghsiExp2
  rw [pow_two]

@[simp] theorem replicaBridgeInteraction_flip_right
    (sites : I -> V) (a b : ConfigSpace V) :
    replicaBridgeInteraction sites a (FieldGhostDict.flipV b) =
      -replicaBridgeInteraction sites a b := by
  unfold replicaBridgeInteraction
  simp_rw [FieldGhostDict.spin_flipV]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring



theorem ghsiCrossExp2_flip_right
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (F : ConfigSpace V -> ConfigSpace V -> Real) :
    ghsiCrossExp2 G J hf (fun x => -hf x) F =
      ghsiExp2 G J hf (fun a b => F a (FieldGhostDict.flipV b)) := by
  unfold ghsiCrossExp2 ghsiExp2
  rw [ghsvp_ZJ_negField]
  rw [pow_two]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [← Equiv.sum_comp
    (FieldGhostDict.flipV_involutive (V := V)).toPerm]
  apply Finset.sum_congr rfl
  intro b _
  simp only [Function.Involutive.coe_toPerm]
  rw [ghsvp_wJ_negField_flip]


theorem ghsiExp2_eq_cross_flip_right
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real)
    (F : ConfigSpace V -> ConfigSpace V -> Real) :
    ghsiExp2 G J hf F =
      ghsiCrossExp2 G J hf (fun x => -hf x)
        (fun a b => F a (FieldGhostDict.flipV b)) := by
  rw [ghsiCrossExp2_flip_right]
  congr 1
  funext a b
  rw [FieldGhostDict.flipV_involutive]

theorem ghsiCrossExp2_neg
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf₁ hf₂ : V -> Real)
    (F : ConfigSpace V -> ConfigSpace V -> Real) :
    ghsiCrossExp2 G J hf₁ hf₂ (fun a b => -F a b) =
      -ghsiCrossExp2 G J hf₁ hf₂ F := by
  unfold ghsiCrossExp2
  simp_rw [mul_neg]
  simp only [Finset.sum_neg_distrib]
  ring

theorem replicaCrossBridgeMoment_same
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaCrossBridgeMoment G J hf hf sites r =
      replicaBridgeMoment G J hf sites r := by
  unfold replicaCrossBridgeMoment replicaBridgeMoment
  exact ghsiCrossExp2_same G J hf _



theorem replicaBridgeMoment_neg_eq_cross_negField
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeMoment G J hf sites (-r) =
      replicaCrossBridgeMoment G J hf (fun x => -hf x) sites r := by
  unfold replicaBridgeMoment replicaCrossBridgeMoment
  rw [ghsiCrossExp2_flip_right]
  congr 1
  funext a b
  rw [replicaBridgeInteraction_flip_right]
  congr 1
  ring

theorem replicaCrossBridgeMean_same
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaCrossBridgeMean G J hf hf sites r =
      replicaBridgeMean G J hf sites r := by
  unfold replicaCrossBridgeMean replicaBridgeMean
  rw [ghsiCrossExp2_same, replicaCrossBridgeMoment_same]


theorem replicaBridgeMean_neg_eq_neg_cross_negField
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeMean G J hf sites (-r) =
      -replicaCrossBridgeMean G J hf (fun x => -hf x) sites r := by
  unfold replicaBridgeMean replicaCrossBridgeMean
  rw [replicaBridgeMoment_neg_eq_cross_negField]
  rw [ghsiExp2_eq_cross_flip_right]
  rw [show (fun a b =>
      replicaBridgeInteraction sites a (FieldGhostDict.flipV b) *
        Real.exp
          (-r * replicaBridgeInteraction sites a (FieldGhostDict.flipV b))) =
      (fun a b => -(replicaBridgeInteraction sites a b *
        Real.exp (r * replicaBridgeInteraction sites a b))) by
    funext a b
    rw [replicaBridgeInteraction_flip_right]
    rw [show -r * -replicaBridgeInteraction sites a b =
        r * replicaBridgeInteraction sites a b by ring]
    ring]
  rw [ghsiCrossExp2_neg]
  ring

theorem replicaCrossBridgeVariance_same
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaCrossBridgeVariance G J hf hf sites r =
      replicaBridgeVariance G J hf sites r := by
  unfold replicaCrossBridgeVariance replicaBridgeVariance
  rw [ghsiCrossExp2_same, replicaCrossBridgeMoment_same,
    replicaCrossBridgeMean_same]



theorem replicaBridgeVariance_neg_eq_cross_negField
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeVariance G J hf sites (-r) =
      replicaCrossBridgeVariance G J hf (fun x => -hf x) sites r := by
  unfold replicaBridgeVariance replicaCrossBridgeVariance
  rw [replicaBridgeMoment_neg_eq_cross_negField,
    replicaBridgeMean_neg_eq_neg_cross_negField]
  rw [ghsiExp2_eq_cross_flip_right]
  rw [show (fun a b =>
      replicaBridgeInteraction sites a (FieldGhostDict.flipV b) ^ 2 *
        Real.exp
          (-r * replicaBridgeInteraction sites a (FieldGhostDict.flipV b))) =
      (fun a b => replicaBridgeInteraction sites a b ^ 2 *
        Real.exp (r * replicaBridgeInteraction sites a b)) by
    funext a b
    rw [replicaBridgeInteraction_flip_right]
    rw [show -r * -replicaBridgeInteraction sites a b =
        r * replicaBridgeInteraction sites a b by ring]
    ring]
  ring



theorem replicaBridgeVariance_order_iff_crossField
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) :
    replicaBridgeVariance G J hf sites r <=
        replicaBridgeVariance G J hf sites (-r) <->
      replicaCrossBridgeVariance G J hf hf sites r <=
        replicaCrossBridgeVariance G J hf (fun x => -hf x) sites r := by
  rw [replicaCrossBridgeVariance_same,
    replicaBridgeVariance_neg_eq_cross_negField]



theorem replicaBridgeFreeEnergy_le_of_crossField_variance
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (hf : V -> Real) (sites : I -> V)
    (r : Real) (hr : 0 <= r)
    (hcross : forall t, 0 <= t ->
      replicaCrossBridgeVariance G J hf hf sites t <=
        replicaCrossBridgeVariance G J hf (fun x => -hf x) sites t) :
    replicaBridgeFreeEnergy G J hf sites r <=
      2 * r * ∑ i : I,
        (expJ G.edgeFinset J hf (fun s => spin s (sites i))) ^ 2 := by
  apply replicaBridgeFreeEnergy_le_of_variance_order G J hf sites r hr
  intro t ht
  rw [replicaBridgeVariance_order_iff_crossField]
  exact hcross t ht

end

end StatMech.Ising
