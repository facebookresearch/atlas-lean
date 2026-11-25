# Membership in a 2-3 tree

A key $x$ is a member of a 2-3 tree when it is one of the
separator keys stored at its nodes: nothing is a member of a leaf; $x$ is a member of a 2-node
with key $a$ and children $l, r$ when it is a member of $l$, equals $a$, or is a member of $r$;
and $x$ is a member of a 3-node with keys $a, b$ and children $l, m, r$ when it is a member of
$l$, equals $a$, is a member of $m$, equals $b$, or is a member of $r$.

Membership is structural and does not use the ordering invariant.
