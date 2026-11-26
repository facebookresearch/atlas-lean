# Grounded DC angles from the reduced susceptance matrix

Let a network have finitely many nodes and finitely many branches `e`, each with a tail and a head
node, and real branch susceptances `b_e`, `r` a reference node and `p` real nodal injections. The
grounded angles are `θ_r = 0` and, on the other nodes, `θ = L_red⁻¹ p`, where `L_red` is the
[reduced grounded matrix](grounded-laplacian.md) and `p` is restricted to the nodes other than `r`.
The inverse is the total matrix inverse: it is the true inverse when `L_red` is invertible (for
example for [positive susceptances on a connected network](grounded-laplacian-is-unit.md)), and the
zero matrix otherwise, in which case every grounded angle is `0`.
