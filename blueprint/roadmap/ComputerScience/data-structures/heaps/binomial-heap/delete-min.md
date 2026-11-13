# Deleting the minimum of a binomial heap

If the binomial heap $H$ has no trees, there is no
result. Otherwise, remove from the list of trees of $H$ the first tree whose root is minimal; the
result is that root together with the binomial heap whose list of trees is obtained by melding
the children of the removed tree, in reversed order, with the remaining trees.
