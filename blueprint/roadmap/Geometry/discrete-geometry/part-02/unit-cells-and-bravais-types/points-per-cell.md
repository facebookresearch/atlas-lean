# Lattice points per conventional cell

A Bravais lattice $\Lambda$ has a real $3 \times 3$ basis matrix $B$ with $\det B \ne 0$, primitive
vectors the columns of $B$, and lattice $L(\Lambda) = \{Bn : n \in \mathbb{Z}^3\}$. For Bravais
lattices $\Lambda_c, \Lambda_f$, the number of points per cell is the index of
$L(\Lambda_c) \cap L(\Lambda_f)$ in $L(\Lambda_f)$, the cardinality of the quotient group
$L(\Lambda_f)/(L(\Lambda_c) \cap L(\Lambda_f))$; when the index is infinite the value is $0$, by the
convention that an infinite set has natural-number cardinality $0$. When $\Lambda_c$ is a
[sublattice](is-sublattice-of.md) of $\Lambda_f$, it is the index of $L(\Lambda_c)$ in
$L(\Lambda_f)$, and $|\det B_c|/|\det B_f|$ equals it
([volume ratio](points-per-cell-eq-volume-ratio.md)). It is a quotient count, not the number of
lattice points in the closed [conventional cell](conventional-cell.md), whose boundary points
neighbouring cells share.
