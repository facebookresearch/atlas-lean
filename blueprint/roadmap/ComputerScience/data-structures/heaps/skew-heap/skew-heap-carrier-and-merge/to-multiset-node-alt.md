# To Multiset node alt

The book's (§14.1) order for `mset_tree` of a node:
`{#a#} + mset_tree l + mset_tree r`. Isabelle/HOL's `mset_tree`
puts the singleton in the middle (`toMultiset_node`); the two agree
because multiset addition is commutative.
