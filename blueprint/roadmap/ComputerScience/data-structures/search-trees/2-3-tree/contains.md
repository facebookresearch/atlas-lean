# Search in a 2-3 tree

For a linearly ordered key type, searching a 2-3 tree for a key
$x$ returns false at a leaf. At a 2-node with key $a$, it searches the left subtree if $x < a$,
otherwise the right subtree if $a < x$, and otherwise returns true. At a 3-node with keys $a$
and $b$, it searches the left subtree if $x < a$; otherwise, if $a < x$, it searches the
middle subtree if $x < b$, otherwise the right subtree if $b < x$, and otherwise returns true;
if neither $x < a$ nor $a < x$, it returns true.
