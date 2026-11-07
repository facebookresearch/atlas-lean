# Admixture graph

An admixture graph on the nodes `V` (Patterson et al. 2012): a rooted directed acyclic
graph in which every non-root node has one or two parents, with admixture proportions.

* `parents X` are the parents of `X`, the root has none, every other node has one or two;
* `prop X Y` is the probability that a lineage in `X` descends from parent `Y`: nonnegative,
  summing to `1` over the parents of a non-root node, and `0` off the parent set;
* the parent relation is well founded, i.e. the graph is acyclic (`V` is finite in all
  results).
