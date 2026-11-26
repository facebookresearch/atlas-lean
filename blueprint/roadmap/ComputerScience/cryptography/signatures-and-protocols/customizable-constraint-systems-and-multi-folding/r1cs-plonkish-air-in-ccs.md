# R1CS, Plonkish and AIR constraint systems embed into CCS

(i) An R1CS structure $(A,B,C)$ is the CCS with $t=3$, $q=2$, $d=2$, $M_1=A$, $M_2=B$, $M_3=C$, $S_1=\{1,2\}$, $S_2=\{3\}$, $c_1=1$, $c_2=-1$. (ii) A Plonkish circuit whose gate is a fixed multivariate polynomial $g$ of total degree $d$ in $t$ wire values, applied row-wise with selector constants, embeds into a CCS with one matrix $M_j$ per wire column (selecting, for each row, the referenced entry of $z$) and one multiset $S_i$ per monomial of $g$, with the monomial coefficient as $c_i$. (iii) An AIR with transition constraints of degree $d$ over two consecutive rows embeds similarly with matrices selecting the current and next rows. In all cases the CCS has the same number of constraints and witness entries as the source system, so the embeddings incur no asymptotic overhead.

## Proof sketch

For R1CS, $c_1(M_1z\circ M_2z)+c_2M_3z=Az\circ Bz-Cz$. For a Plonkish gate $g=\sum_i c_i\prod_{j\in S_i}w_j$, setting $M_jz$ to the vector of $j$-th wire values over all rows makes the CCS equation the row-wise evaluation of $g$; copy constraints become shared indices of $z$. AIR rows are handled by the same selection, with row shifts encoded in the matrices.

## Depends on

- [Customizable constraint systems](customizable-constraint-system.md)
- [PLONK gate equations with copy constraints](../plonkish-polynomial-iops/plonk-constraint-system.md)

## Proof depends on

- [Customizable constraint systems](customizable-constraint-system.md)

## Sources

- Srinath Setty, Justin Thaler, Riad Wahby, "Customizable Constraint Systems for Succinct Arguments", IACR ePrint 2023/552 (2023).
