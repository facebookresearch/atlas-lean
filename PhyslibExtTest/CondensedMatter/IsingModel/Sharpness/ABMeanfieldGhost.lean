/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABMeanfieldGhost

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABMeanfieldGhost`

* `abmg_meanfield_finite` on the two-vertex complete graph, applied under its `φ(S) ≥ m`
  hypothesis;
* `abmg_meanfield_target_finite` with the ghost target `{none}`, and the general form;
* the hypotheses on couplings hold for the unit coupling.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABMeanfieldGhost

open _root_.StatMech _root_.StatMech.Sharpness

-- The mean-field inequality on `K₂` with unit couplings.
example (β h m : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hm : ∀ S : Finset (Option (Fin 2)), some 0 ∈ S →
      (mpiSurfaceEvent (withGhost (⊤ : SimpleGraph (Fin 2))) {none} S).Nonempty →
        m ≤ abmgPhi ⊤ (fun _ => 1) 0 β h S) :
    m * (1 - abfaMag (⊤ : SimpleGraph (Fin 2)) (fun _ => 1) 0 β h) ≤
      β * deriv (fun b => abfaMag (⊤ : SimpleGraph (Fin 2)) (fun _ => 1) 0 b h) β :=
  abmg_meanfield_finite ⊤ _ 0 β h m (fun _ _ => zero_le_one) hβ hh hm

-- The general-target form.
example {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V → ℝ) (o : V) (B : Set (Option V)) (β h m : ℝ) (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
    (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hm : ∀ S : Finset (Option V), some o ∈ S → (mpiSurfaceEvent (withGhost G) B S).Nonempty →
      m ≤ abmgTargetPhi G J o B β h S) :
    m * (1 - abmgTargetMag G J o B β h) ≤ β * deriv (fun b => abmgTargetMag G J o B b h) β :=
  abmg_meanfield_target_finite G J o B β h m hJ hβ hh hm

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABMeanfieldGhost
