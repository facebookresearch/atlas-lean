# Fibonacci subtree size from link order

In a finite tree view, suppose that everywhere
in the subtree, the child at zero-based link position `i` has current rank at least `i - 1`.
Then the number of nodes in the view, counting its root, is at least Fibonacci number `k + 2`
for root rank `k`. The positional hypothesis, not heap order alone, drives this implication.
