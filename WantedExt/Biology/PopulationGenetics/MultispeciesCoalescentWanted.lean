/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The multispecies coalescent: deferred statements

`MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent` defines the law of the gene tree
under the multispecies coalescent (`geneTreeProb`) and evaluates it on three- and four-species
trees. Rosenberg's clade probability is deferred for every sample size; the module proves it
for `m ≤ 5` by kernel evaluation (`randomJoining_isClade_of_le_five`).

Source: N. A. Rosenberg, "The shapes of neutral gene genealogies
in two species: probabilities of monophyly, paraphyly, and polyphyly in a coalescent model",
Evolution 57 (2003) 1465–1477.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescentWanted

open MeasureTheory MathlibExt.Biology.PopulationGenetics.Coalescent
open MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescent

/-- **Clade probability** (Rosenberg 2003): under random joining, a fixed set of `k` among `m`
genes, `1 ≤ k < m`, is a clade with probability `2m / (k (k + 1) C(m, k))`.

Source: Rosenberg (2003). -/
theorem_wanted randomJoining_isClade {m : ℕ} (S : Finset (Fin m)) (hS : 1 ≤ S.card)
    (hSm : S.card < m) :
    (randomJoining m).real {h | IsClade h S} =
      2 * m / (S.card * (S.card + 1) * (m.choose S.card : ℝ))

end MathlibExt.Biology.PopulationGenetics.MultispeciesCoalescentWanted
