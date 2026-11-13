# Deleting the minimum of a Fibonacci heap

If the root list of the heap is empty, the result
is nothing. Otherwise the first tree of the root list whose root is minimal is removed, and the
result is its root value together with the heap whose root list is the consolidation of the
removed tree's children followed by the remaining trees, and whose cached minimum is the minimum
root of this consolidated forest.
