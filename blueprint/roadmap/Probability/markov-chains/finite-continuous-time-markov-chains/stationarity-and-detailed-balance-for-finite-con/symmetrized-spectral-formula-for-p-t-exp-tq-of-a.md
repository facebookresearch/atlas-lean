# Spectral formula for a reversible rate matrix

Let $Q$ be a real rate matrix on a finite nonempty set: its off-diagonal
entries are nonnegative and its row sums are zero. Let $\pi$ be a strictly
positive probability vector in [detailed balance](is-detailed-balance.md)
with $Q$. Put $D=\operatorname{diag}(\pi)$.
Then $S=D^{1/2}QD^{-1/2}$ is real symmetric. There is a real orthogonal
$U$ and a real diagonal $\Lambda$ with $S=U\Lambda U^\top$, and the
[transition function](../the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md) satisfies

$$e^{tQ}=D^{-1/2}Ue^{t\Lambda}U^\top D^{1/2}\qquad(t\ge0).$$

All eigenvalues are nonpositive. No irreducibility is required; the zero
eigenvalue need not be simple. At $t=0$ the formula is the identity.
For the four-state Jukes–Cantor matrix with off-diagonal rate $\alpha\ge0$,
it gives $P_{ii}(t)=1/4+3e^{-4\alpha t}/4$ and
$P_{ij}(t)=(1-e^{-4\alpha t})/4$ for $i\ne j$.
For $\alpha=0$ all four eigenvalues are zero.

## Depends on

- [Detailed balance](is-detailed-balance.md)
- [Finite transition function](../the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md)

## Background

- [GTR rate matrices](../../../../Biology/phylogenetics/time-reversible-nucleotide-substitution-models/is-rate-matrix-gtr-rate.md)

## Expansion

Detailed balance gives $S_{ij}=S_{ji}$.
Real orthogonal diagonalization follows by maximizing the Rayleigh
quotient on the unit sphere: a maximizing vector is an eigenvector,
its orthogonal complement is invariant by symmetry, and induction gives
an orthonormal eigenbasis. Similarity commutes with every matrix power
and therefore with the absolutely convergent exponential series.
For $v_i=\sqrt{\pi_i}z_i$, row sums and detailed balance give
$v^\top Sv=-\frac12\sum_{i,j}\pi_iq_{ij}(z_i-z_j)^2\le0$,
so each real eigenvalue is nonpositive.
For Jukes–Cantor, the projection onto constants has eigenvalue zero;
its orthogonal complement has eigenvalue $-4\alpha$, giving both entries.

## Sources

- C. Moler and C. Van Loan, "Nineteen dubious ways to compute the exponential of a matrix, twenty-five years later", SIAM Review 45 (2003), 3–49 (eigenvector methods). The symmetrization is derived above.
