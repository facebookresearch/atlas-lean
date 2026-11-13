# Deleting the successor in a singly linked list

Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node whose next
pointer is an identity below $n$ or NIL, and let $y$ be an identity such that $s(y)$ is a node.
Deleting after $y$ returns the store that agrees with $s$ except at $y$, where it holds the node
$s(y)$ with its next pointer replaced as follows: if the next pointer of $s(y)$ is an identity $m$
and $s(m)$ is a node, the new next pointer is the next pointer of $s(m)$; otherwise it is NIL.

The removed node stays allocated in the store; at the tail the links are unchanged.
