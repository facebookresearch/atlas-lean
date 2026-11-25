# Cells after deleting a successor

Fix a capacity $n$, let $s$ be a store assigning to each
identity below $n$ either nothing or a singly linked list node, let $y$ be an identity such that
$s(y)$ is a node, and let $s'$ be the store obtained from $s$ by deleting the successor of $y$.
Let $c$ be the node $s(y)$ with its next pointer replaced by the next pointer of $s(m)$ if the
next pointer of $s(y)$ is an identity $m$ such that $s(m)$ is a node, and by NIL otherwise. Then
for every identity $z$, $s'(z)$ is the node $c$ if $z = y$, and $s'(z) = s(z)$ if $z \ne y$.
