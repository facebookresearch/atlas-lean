# The multispecies coalescent

**The multispecies coalescent** (Pamilo & Nei 1988; Degnan & Salter 2005), one lineage
sampled per species: the probability that the gene tree, given by its set of clusters, lies in
the event `E`. Below the root, each branch population runs Kingman's coalescent for the
branch length (`branchStep`); in the root population all remaining lineages coalesce by
random joining. The definition accepts any real branch lengths; it is a probability law on
species trees with nonnegative branch lengths (`geneTreeProb_nonneg`, `geneTreeProb_or`,
`geneTreeProb_true`), and only a signed weight otherwise (with internal branch `-1`, the
matching three-species gene tree gets `1 - (2/3) e < 0`).
