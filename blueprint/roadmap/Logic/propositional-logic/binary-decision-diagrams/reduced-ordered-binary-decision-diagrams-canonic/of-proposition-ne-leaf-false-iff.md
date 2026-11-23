# Satisfiable iff the BDD is not the false leaf

For a proposition $A$ over
natural-number atoms, the binary decision diagram of $A$ is not the leaf false if and only if
some valuation $\sigma : \mathbb{N} \to \mathrm{Bool}$ makes $A$ true.

Both sides always hold: the valuation that makes every atom true satisfies every proposition
built from atoms by conjunction, disjunction and implication.
