# Autocatalytic cores are Metzler unstable-positive feedbacks

Work in the setting of [unstable cores of Child-Selection matrices](unstable-cores-of-child-selection-matrices.md): a reaction network $\Gamma=(M,E)$ with stoichiometric matrix $S$ and a parameter-rich kinetic model. For $\kappa\subseteq M$ and $\iota\subseteq E$, a $|\kappa|\times|\iota|$ submatrix $S'$ of $S$ is *autocatalytic* if

1. there is $v\in\mathbb R^{|\iota|}_{>0}$ with $S'v>0$ (all species in $\kappa$ can be produced simultaneously by the reactions in $\iota$), and
2. every reaction $j\in\iota$ has a reactant $m\in\kappa$ and a product $\tilde m\in\kappa$ (not necessarily distinct).

An *autocatalytic core* is an autocatalytic submatrix containing no proper autocatalytic submatrix. The network is *autocatalytic* if it has an autocatalytic submatrix.

**Theorem.** A submatrix $\tilde A$ of $S$ is an autocatalytic core if and only if $\tilde A$ is square, of size $k\times k$, and its columns can be reordered into a Child-Selection matrix $A=S[\boldsymbol\kappa]$ that is a Metzler matrix (nonnegative off-diagonal entries) and an unstable-positive feedback, that is, a minimal Hurwitz-unstable Child-Selection matrix with $\operatorname{sign}\det A=(-1)^{k-1}$.

**Consequences.**

- No unstable-negative feedback is an autocatalytic matrix.
- A network is autocatalytic if and only if some Child-Selection matrix $S[\boldsymbol\kappa]$ is a Hurwitz-unstable Metzler matrix.
- Every autocatalytic network admits instability: some positive equilibrium has a Hurwitz-unstable Jacobian for suitable parameters.
- A $k\times k$ Metzler matrix $A$ with negative diagonal is an autocatalytic core if and only if $\operatorname{sign}\det A=(-1)^{k-1}$ and every proper nonempty principal submatrix $A[\kappa']$ has $\operatorname{sign}\det A[\kappa']=(-1)^{|\kappa'|}$ or $\det A[\kappa']=0$.

The proofs pass through the non-explicitly-catalytic extension of the network, which replaces each explicitly catalytic reaction by a two-step mechanism with an intermediate and preserves autocatalytic cores.

## Depends on

- [Unstable cores of Child-Selection matrices](unstable-cores-of-child-selection-matrices.md)

## Expansion

For an invertible irreducible Metzler matrix $A$, Hurwitz instability is equivalent to the existence of $v>0$ with $Av>0$ (Perron-Frobenius applied to $A+cI$). An autocatalytic core of a network without explicit catalysts is square, invertible and irreducible, and each species row has a unique negative entry; reordering columns to put these on the diagonal yields a Metzler Child-Selection matrix with negative diagonal. Minimality of the autocatalytic core then translates into minimality of Hurwitz instability among principal submatrices, and the sign of the determinant is forced by the single real positive Perron eigenvalue. Instability of the network follows from the Child-Selection instability criterion.

## Sources

- N. Vassena and P. F. Stadler, "Unstable Cores are the source of instability in chemical reaction networks", *Proceedings of the Royal Society A: Mathematical, Physical and Engineering Sciences* 480(2285) (2024), 20230694, Definitions 22-23 (autocatalytic matrix and core), Theorem 24, Corollaries 26-28, and Section 11 (non-explicitly-catalytic extensions, Lemma 35, Lemma 38, Lemma 40, Lemma 41, Lemma 42), <https://doi.org/10.1098/rspa.2023.0694> (preprint arXiv:2308.11486).
