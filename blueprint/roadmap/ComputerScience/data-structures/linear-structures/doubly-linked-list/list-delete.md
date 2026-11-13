# Deletion from a doubly linked list

Let the store be an array of cells, each either empty
or holding a node with a payload and optional next and previous pointers to cells, let $h$ be
the optional head pointer, and let $x$ be a cell holding a node such that each cell named by its
previous or next pointer also holds a node. Following CLRS `LIST-DELETE`, deleting $x$ returns a
new store and head as follows. If the node at $x$ has a previous pointer $p$, the next pointer of
the node at $p$ is set to the next pointer of $x$ and the head stays $h$; otherwise the head
becomes the next pointer of $x$. Then, if the node at $x$ has a next pointer $s$, the previous
pointer of the node at $s$ in the store from the first step is set to the previous pointer of $x$.
The computation is charged one unit for each of the two NIL tests and one unit for each executed
pointer or head assignment, so three or four units in total.

The record stored at $x$ is kept and no cell is freed; list consistency is needed only for
correctness, not to run the procedure.
