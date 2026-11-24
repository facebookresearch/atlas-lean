# Inorder traversal of a possibly double-black tree

The inorder traversal of a red-black
tree whose root may be double black ignores the double-black mark: a genuine tree gives its
inorder traversal, the double-black empty tree gives the empty list, and a double-black node with
left child $l$, key $k$ and right child $r$ gives the inorder traversal of $l$, followed by $k$,
followed by the inorder traversal of $r$.
