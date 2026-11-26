# Building a 2-3 tree from a list

For linearly ordered keys, the 2-3 tree root built from
a list is defined by recursion: the empty list gives the empty 2-3 tree, and a list with head $x$
and tail $xs$ gives the result of inserting $x$ into the root built from $xs$. Thus the elements
are inserted into the empty tree from the last to the first.
