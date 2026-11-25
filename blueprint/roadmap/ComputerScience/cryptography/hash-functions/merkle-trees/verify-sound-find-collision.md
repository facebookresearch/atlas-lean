# Constructive soundness of Merkle inclusion proofs

Let $r$ be the root of a list of $n$ leaves. If a path for $x$ at position $i$ verifies the claim that
leaf $i$ of a tree with $n$ leaves and root $r$ is $x$, then leaf $i$ of the list is $x$, or the search on
the forged and actual paths returns a collision pair of $h$.
