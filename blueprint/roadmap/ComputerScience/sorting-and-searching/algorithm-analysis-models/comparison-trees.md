# Comparison trees

A *comparison tree* on $n$ keys is a finite binary tree whose internal nodes are labelled by comparisons $x_i < x_j$ and whose leaves are labelled by outputs (a permutation for sorting, an index or answer for searching). On an input of distinct keys the tree is run by following, from the root, the branch given by the true answer at each node, and its output is the label of the leaf reached. The cost on an input is the length of the root-to-leaf path it follows, and the worst-case cost is the maximum of this length over inputs of distinct keys, that is, the greatest depth of a leaf reached by some input. It equals the depth of the tree when every leaf is reached by some input, which can always be arranged by pruning unreachable branches without increasing any input's cost. An algorithm in the comparison model accesses the keys only through such comparisons.

## Expansion

This page becomes ready once:

- The statement must be checked against the cited sources, which have not been opened

## Sources

- J. Erickson, *Algorithms*, 1st ed., 2019, <https://jeffe.cs.illinois.edu/teaching/algorithms/>
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*, 4th ed., MIT Press, 2022
