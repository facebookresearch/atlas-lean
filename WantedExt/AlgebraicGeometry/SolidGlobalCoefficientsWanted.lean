/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Condensed.GlobalSolidCoefficientLimits
public import MathlibExt.Condensed.PerfectoidIntegralVSites

/-!
# Actual local and global solid coefficient construction requests

The coefficients are actual untilt plus rings. Local maps retain their
native derived extension, analytic/adic units and all homogeneous DG
classes. Global values and affine/hypercover comparisons use the fixed
native categorical limits. Hyperdescent and affine identification are
outputs of construction requests.

Strict DG pullbacks cannot be requested between arbitrary, independently chosen compact
dictionaries (for instance a source dictionary containing a literal zero object and a target
dictionary padded by a contractible complex admit no strictly unital functor). The requests below
therefore choose the dictionaries together with the pullbacks: `localSolidPullback` chooses the
target model with its pullback, and `globalSolidCoefficients` chooses its local diagram, which later
constructions use through its first component. The descent and affine statements concern the limit
of that chosen diagram; its identification with the geometric pullbacks is only arrowwise (see
`GlobalSolidCoefficientLimits.LocalDiagram`), and a homotopy-coherent identification is not
requested here.

Source: Anschuetz--Mann, arXiv:2403.01951v2, Theorems 1.1 and 4.7,
Definitions 2.3--2.4 and 4.2.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SolidGlobalCoefficients

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.PerfectoidSliceSites
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open MathlibExt.Condensed.LocalSolidCoefficientModels
open MathlibExt.Condensed.GlobalSolidCoefficientLimits

/-- Descent of the literal continuous-section presheaf of marked untilt plus rings. -/
public theorem_wanted integralSectionsDescent (p : ℕ) [Fact p.Prime]
    (F : VSheaf p) (D : MathlibExt.Condensed.PerfectoidIntegralVSites.UntiltingDiagram p F) :
    Presheaf.IsSheaf (MathlibExt.Condensed.PerfectoidIntegralVSites.coefficientTopology F)
      (MathlibExt.Condensed.PerfectoidIntegralVSites.integralPresheaf D)

/-- Continuity of the actual compact-test inclusion in the coefficient product site. -/
public theorem_wanted compactTestContinuity (p : ℕ) [Fact p.Prime]
    (F : VSheaf p) (T : AffineTest p F) :
    (MathlibExt.Condensed.PerfectoidIntegralVSites.compactTests T).IsContinuous
      (coherentTopology CompHaus.{0})
      (MathlibExt.Condensed.PerfectoidIntegralVSites.coefficientTopology F)

/-- Actual local modified coefficients, including all source-normalized stable units. -/
public def_wanted localSolidCoefficients (p : ℕ) [Fact p.Prime] (P : AffineUntilting p) :
    LocalModel p P

/-- Actual geometric coefficient pullback and the complete scalar-changing module adjunction, for
a target local model chosen together with the pullback (a strict pullback between arbitrary given
models need not exist). -/
public def_wanted localSolidPullback (p : ℕ) [Fact p.Prime]
    {P Q : AffineUntilting p} (f : P ⟶ Q) (MQ : LocalModel p Q) :
    Σ MP : LocalModel p P, PullbackModel p f MP MQ

/-- Assemble normalized global coefficients with actual affine identification and v-hyperdescent,
together with the local coefficient diagram (dictionaries, strict pullbacks and assembled diagram,
chosen jointly) whose limit they are. -/
public def_wanted globalSolidCoefficients (p : ℕ) [Fact p.Prime] :
    Σ G : LocalDiagram p,
      {M : GlobalModel p G // IsAffineNormalized p M ∧ IsHypercomplete p M}

/-- A model for the actual whole stack chart diagram retains all stabilizer arrows. -/
public def_wanted stackCoefficientLimit (p : ℕ) [Fact p.Prime]
    (G : LocalDiagram p) (F : MathlibExt.AlgebraicGeometry.PerfectoidVStackSites.PerfdVStack p) :
    MathlibExt.CategoryTheory.CategoricalCoefficientLimits.DiagramModel.{2, 1, 1}
      (stackDiagram p G F)

end WantedExt.AlgebraicGeometry.SolidGlobalCoefficients
