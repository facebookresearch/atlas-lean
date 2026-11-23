/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.SemialgebraicTriviality

/-!
# Hardt triviality for general continuous semialgebraic maps

The set and graph conditions are finite Boolean polynomial conditions.
The output has actual Euclidean homeomorphisms to products with the
map's genuine reference fibres, with semialgebraic graphs in both
directions and literal projection/reference normalization.

Closure of real semialgebraic sets under coordinate projection
(Tarski--Seidenberg) is requested first, as the instance
`HasSemialgebraicProjections ℝ`; it is proved in the TauCeti source by
cylindrical algebraic decomposition but not ported. Hardt's theorem is then
requested without any projection hypothesis: there is no polynomial,
properness, compactness or dimension restriction on the continuous
semialgebraic map.

Sources: R. M. Hardt, *Semi-Algebraic Local-Triviality in Semi-Algebraic
Mappings*, Amer. J. Math. 102 (1980), 291--302,
https://doi.org/10.2307/2374240, main triviality theorem; for
Tarski--Seidenberg, S. Basu, R. Pollack and M.-F. Roy, *Algorithms in Real
Algebraic Geometry*, second edition, Chapter 2,
https://doi.org/10.1007/3-540-33099-2.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SemialgebraicTriviality

open TauCeti MathlibExt.AlgebraicGeometry.SemialgebraicTriviality

/-- Tarski--Seidenberg over the reals: the projection of a semialgebraic set is
semialgebraic. -/
public instance_wanted realSemialgebraicProjections : HasSemialgebraicProjections ℝ

/-- Every continuous semialgebraic map has a finite normalized trivialization
over actual semialgebraic pieces of its image. -/
public def_wanted hardt_trivialization
    (m n : ℕ) (s : Set (RealSpace m)) (f : RealSpace m → RealSpace n)
    (semialgebraic : IsSemialgebraicOn f s) (continuous : ContinuousOn f s) :
    HardtTrivialization s f

end WantedExt.AlgebraicGeometry.SemialgebraicTriviality
