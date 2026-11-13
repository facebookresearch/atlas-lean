/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Common graphs of large chromatic number (Open Problem Garden 59952)

Open Problem Garden, Chromatic Number of Common Graphs (Hatami, Hladký, Kráľ, Norine, Razborov): do
common graphs have bounded chromatic number?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.GraphTheory.CommonGraphsChromaticNumberOpenGardenProblem59952Wanted

/-!
Source: Open Problem Garden, Chromatic Number of Common Graphs (node 59952; H. Hatami, J. Hladký, D.
Kráľ, S. Norine and A. Razborov),
http://www.openproblemgarden.org/op/chromatic_number_of_common_graphs. UnsolvedMath record
UM-00003135 (`OPG-59952`), dataset ulamai/UnsolvedMath v1.8.0.

The source defers the formal definition of common graphs to Hatami et al.; it is taken from Kráľ,
Volec and Wei, Section 2: `H` is common if `2 ^ (1 - e(H)) ≤ t(H, W) + t(H, 1 - W)` for every
graphon `W`, where `t(H, W) = ∫_{[0,1]^{V(H)}} ∏_{uv ∈ E(H)} W(x_u, x_v) dx`. A graphon is encoded
as a jointly measurable symmetric `W : ℝ → ℝ → ℝ` with values in `[0, 1]`, of which only the values
on `[0, 1]²` enter `t`. Graphs are finite simple graphs on `Fin k`, and "bounded" means one bound
`C` for all common graphs.
-/

open MeasureTheory

/-- A graphon, as a function on `ℝ²` of which only the values on the unit square `[0, 1]²` are
used: a jointly measurable symmetric function with values in `[0, 1]`. -/
def IsGraphon (W : ℝ → ℝ → ℝ) : Prop :=
  Measurable (Function.uncurry W) ∧ ∀ x y, W x y = W y x ∧ 0 ≤ W x y ∧ W x y ≤ 1

open Classical in
/-- The homomorphism density `t(H, W) = ∫_{[0,1]^{V(H)}} ∏_{uv ∈ E(H)} W(x_u, x_v) dx` of a graph
`H` on `Fin k` in a graphon `W` (Kráľ, Volec and Wei, equation (2)); each edge `uv` of `H` is taken
once, as the pair `(u, v)` with `u < v`. -/
noncomputable def homDensity {k : ℕ} (H : SimpleGraph (Fin k)) (W : ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in Set.univ.pi (fun _ : Fin k => Set.Icc (0 : ℝ) 1),
    ∏ p ∈ Finset.univ.filter (fun p : Fin k × Fin k => p.1 < p.2 ∧ H.Adj p.1 p.2),
      W (x p.1) (x p.2)

/-- `H` is common: `2 ^ (1 - e(H)) ≤ t(H, W) + t(H, 1 - W)` for every graphon `W` (Kráľ, Volec and
Wei, Section 2). -/
def IsCommon {k : ℕ} (H : SimpleGraph (Fin k)) : Prop :=
  ∀ W : ℝ → ℝ → ℝ, IsGraphon W →
    2 / 2 ^ H.edgeSet.ncard ≤ homDensity H W + homDensity H (fun x y => 1 - W x y)

/-- The question of Hatami, Hladký, Kráľ, Norine and Razborov, with the answer "no": common
graphs have bounded chromatic number, i.e. some `C` bounds the chromatic number of every common
graph. -/
def commonGraphsBoundedChromatic : Prop :=
  ∃ C : ℕ, ∀ (k : ℕ) (H : SimpleGraph (Fin k)), IsCommon H → H.chromaticNumber ≤ C

/--
Resolved false: Kráľ, Volec and Wei constructed, for every `ℓ`, a connected common graph with
chromatic number `ℓ`, so no bound on the chromatic number of common graphs exists. Source: Open
Problem Garden, Chromatic Number of Common Graphs (node 59952; H. Hatami, J. Hladký, D. Kráľ, S.
Norine and A. Razborov), http://www.openproblemgarden.org/op/chromatic_number_of_common_graphs;
resolution: D. Kráľ, J. Volec and F. Wei, Common graphs with arbitrary chromatic number, Compos.
Math. 161 (2025), 594-634, doi:10.1112/S0010437X24007681; arXiv:2206.05800, Theorem 1: for every ℓ ∈
N there exists a connected common graph with chromatic number ℓ; the abstract says this answers the
question of Hatami, Hladký, Kráľ, Norine and Razborov and Problem 2.28 of Conlon, Fox and Sudakov,
https://doi.org/10.1112/S0010437X24007681.
-/
public theorem_wanted commonGraphsBoundedChromatic_refuted : ¬ commonGraphsBoundedChromatic

end MathlibExt.GraphTheory.CommonGraphsChromaticNumberOpenGardenProblem59952Wanted
