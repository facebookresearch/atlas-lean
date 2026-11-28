/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# POLARITY ON PLANAR TRIANGLE-FREE GRAPHS OF MAXIMUM DEGREE 3: definitions

Source:
V. B. Le and R. Nevries, "Complexity and algorithms for recognizing polar and monopolar graphs",
Theoretical Computer Science 528 (2014), 1-11, doi:10.1016/j.tcs.2014.01.032;
V. B. Le and R. Nevries, "Recognizing polar planar graphs using new results for monopolarity",
Algorithms and Computation (ISAAC 2011), Lecture Notes in Computer Science 7074, Springer (2011),
120-129, doi:10.1007/978-3-642-25591-5_14 (introduction: "NP-completeness for monopolarity and
polarity on planar graphs and triangle-free graphs of maximum degree 3");
ISGCI, *Information System on Graph Classes and their Inclusions*, class "maximum degree 3 ∩
planar ∩ triangle-free" (gc_1274), problem Polarity: NP-complete, with the reference to Le and
Nevries (2014).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MonopolarityTriangleFreePlanarSubcubicDefs
public import CSLibExt.Complexity.NPComplete.PolarityTriangleFreeDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PolarityPlanarSubcubicTriangleFree

open MetaMathlibExt.Complexity.NPComplete.PolarityTriangleFree
  (PolarityTriangleFreeInstance IsPolar PolarityTriangleFreeFeasible)

open Classical in
/-- POLARITY ON PLANAR TRIANGLE-FREE GRAPHS OF MAXIMUM DEGREE 3 as a decision problem over
bitstrings. -/
noncomputable def polarityPlanarSubcubicTriangleFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PolarityTriangleFreeInstance) x with
  | some i => decide (MonopolarityTriangleFreePlanarSubcubic.WellFormed i ∧
      PolarityTriangleFreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PolarityPlanarSubcubicTriangleFree
