# Deleting a successor leaves other cells unchanged

Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, let $y$ be an
identity such that $s(y)$ is a node, and let $s'$ be the store obtained from $s$ by deleting the
successor of $y$. Then $s'(z) = s(z)$ for every identity $z \ne y$.
