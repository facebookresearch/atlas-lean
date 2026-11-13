# Cartesian tree of a list

For a list $xs$ over a linear order, the Cartesian tree of $xs$
is the result of the fuel-bounded Cartesian tree construction on $xs$ with fuel equal to the
length of $xs$. So the empty list gives the empty tree, and otherwise the root is the minimum $m$
of $xs$, the left subtree is built in the same way from the elements before the first occurrence
of $m$, and the right subtree from the elements after that occurrence.

Its inorder traversal is $xs$ and it is min-heap ordered.
