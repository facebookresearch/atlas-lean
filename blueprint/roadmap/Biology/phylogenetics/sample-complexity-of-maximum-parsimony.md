# Sample complexity of maximum parsimony

Does maximum parsimony recover large trees from only logarithmically many sites in a sufficiently short, comparable-branch regime? General consistency is false under model misspecification or problematic branch configurations, so those restrictions matter.

## What would settle it

Steel's question PC2: for sequences generated independently by a symmetric substitution process (for example the two-state or Jukes–Cantor model) on fully resolved trees, with branch length the expected number of substitutions on an edge, is it true that for every ε > 0 and K ≥ 1 there are constants a, b with 0 < a < b < 1/2 and C > 0 such that, for every fully resolved tree on any number n of leaves whose branch lengths all lie between a and b and have pairwise ratios at most K, maximum parsimony returns the true tree with probability at least $1-\varepsilon$ whenever the sequence length is at least $C \log n / a^2$? A resolution specifies how ties are resolved.

## Status

The cited sources pose this as an open question in the versions cited; this page does not certify its present status. The supporting open-problem statement is older or its status evidence is incomplete; check later literature before relying on it.

Steel lists this as question PC2 in the July 2018 update of his problem list.

This page records the cited research question and asserts no theorem or present-status certification.

## Sources

- M. Steel, *Phylogenetics: challenges and conjectures*, problem list, update of July 2018, PC2. <https://www.math.canterbury.ac.nz/~m.steel/Non_UC/files/research/conjectures_updated.pdf>
