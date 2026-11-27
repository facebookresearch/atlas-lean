# Minimum deletion on a forest

Given a list of Fibonacci trees over a linearly ordered type,
the result is nothing if the list is empty. Otherwise the first tree whose root is minimal is
removed, and the result is its root value together with the consolidation of the forest made of
the removed tree's children followed by the remaining trees.

This is the forest-level computation behind deleting the minimum of a Fibonacci heap, without the
validity proofs.
