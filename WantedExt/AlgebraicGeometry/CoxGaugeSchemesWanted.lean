/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CoxGaugeSchemes

/-!
# Restrict the represented Cox action to the irrelevant open

Reference: Cox, alg-geom/9210008v3, Theorem 2.1(i).
The group algebra, Spec product and ambient coaction are already defined.
This request constructs the normalized restriction; quotient universality
and simplicial orbit fibres remain the distinct existing Wanted statements.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CoxGaugeSchemesWanted

open MathlibExt.AlgebraicGeometry MathlibExt.AlgebraicGeometry.CoxGaugeSchemes

open CategoryTheory CategoryTheory.Limits FiniteToricCoordinates CoxGradedSheaves
  CoxQuotientGeometry

def_wanted cox_open_action {n : ℕ} {F : FiniteFan n} (R : Rays F) : OpenAction R

def_wanted cox_open_action_points {n : ℕ} {F : FiniteFan n} (R : Rays F)
    (G : OpenAction R) :
    {A : GaugeAction R // ∀ (S : CommAlgCat.{0} ℂ) (g : Gauge R S)
      (p : testScheme S ⟶ openScheme R),
      (A.act S g p).left =
        pullback.lift ((affinePoints R S).symm g).left p.left
          (by rw [((affinePoints R S).symm g).w, p.w]) ≫ G.map}

end WantedExt.AlgebraicGeometry.CoxGaugeSchemesWanted
