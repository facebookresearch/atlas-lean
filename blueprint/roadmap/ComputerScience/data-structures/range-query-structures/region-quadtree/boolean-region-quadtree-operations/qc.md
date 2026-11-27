# Compressing branch constructor for Boolean quadtrees

For four Boolean region quadtrees (leaf values true or false) $t_0, t_1, t_2, t_3$, the
compressing branch constructor returns the leaf $L(b)$ if $t_0, t_1, t_2, t_3$ are all leaves
carrying the same value $b$, and the branch $Q(t_0, t_1, t_2, t_3)$ otherwise. It looks only at
the four children; it does not compress them recursively.
