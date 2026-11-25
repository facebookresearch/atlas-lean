# One round of pointer jumping

In one parallel round, every node $v$ whose pointer is a node
$u$ adds the distance of $u$ to its own distance and moves its pointer to the pointer of $u$
(undefined if that of $u$ is); a node whose pointer is undefined keeps its distance and its
undefined pointer.
