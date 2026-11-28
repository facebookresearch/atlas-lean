/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Defs
public import MathlibExt.Geometry.ErdosProblem755

/-!
# Erdős Problem 755 compatibility module

The proved library exports the original counting definitions and the proof of
`conjecture` under their existing names. This legacy path re-exports that API.
-/
