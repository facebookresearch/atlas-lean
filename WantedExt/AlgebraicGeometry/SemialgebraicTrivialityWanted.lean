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

The source-proved real projection provider is a named shared dependency;
this requests neither CAD nor Tarski--Seidenberg again. Provider imports
and the Hardt proof are tracked independently from statement expressiveness.
There is no polynomial, properness, compactness or dimension restriction
on the continuous semialgebraic map.

Source: R. M. Hardt, *Semi-Algebraic Local-Triviality in Semi-Algebraic
Mappings*, Amer. J. Math. 102 (1980), 291--302,
https://doi.org/10.2307/2374240, main triviality theorem.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.SemialgebraicTriviality

open TauCeti MathlibExt.AlgebraicGeometry.SemialgebraicTriviality

/-- Every continuous semialgebraic map has a finite normalized trivialization
over actual semialgebraic pieces of its image. -/
public def_wanted hardt_trivialization [HasSemialgebraicProjections ℝ]
    (m n : ℕ) (s : Set (RealSpace m)) (f : RealSpace m → RealSpace n)
    (semialgebraic : IsSemialgebraicOn f s) (continuous : ContinuousOn f s) :
    HardtTrivialization s f

end WantedExt.AlgebraicGeometry.SemialgebraicTriviality
