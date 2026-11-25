# Insertion by identifier with cost

Let $T$ be an indexed interval tree and let $e$ be an
entry with identifier $i$ and interval $[a, b]$. Inserting $e$ into $T$ first tests $a \le b$. If
$a > b$, it returns no tree, at a cost of one endpoint comparison. Otherwise, if the identifier
index of $T$ maps $i$ to a low endpoint $\ell$, the entry with key $(\ell, i)$ is erased from the
root tree of $T$ by keyed erasure; if $i$ is not in the index, the root tree is kept, at zero
cost. Then $e$ is inserted into the resulting tree by keyed insertion. The result is the indexed
interval tree with this new root tree and with the index updated to map $i$ to $a$, and the cost
is the cost of the erasure plus the cost of the insertion plus one endpoint comparison and two
index operations.
