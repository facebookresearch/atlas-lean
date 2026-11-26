# Erasure by identifier with cost

To erase identifier $i$ from an indexed interval tree,
look $i$ up in the identifier index. If it is absent, the tree is returned unchanged at a cost of
one index operation. If the index maps $i$ to a low endpoint $\ell$, the entry with key
$(\ell, i)$ is erased from the underlying interval tree, $i$ is removed from the index, and the
cost is the cost of the keyed erasure plus two index operations.

When the representation invariant holds, this deletes exactly the stored entry with identifier
$i$.
