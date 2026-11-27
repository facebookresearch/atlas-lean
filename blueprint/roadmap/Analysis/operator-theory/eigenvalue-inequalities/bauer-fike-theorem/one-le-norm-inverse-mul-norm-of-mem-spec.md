# Bauer–Fike exclusion theorem, product form

Let $R$ be a complete normed ring that is an algebra over a field $\mathbb{k}$. If $A, E \in R$ and $\mu \in \mathbb{k}$ lies in the spectrum of $A + E$ but not in the spectrum of $A$, then

$$
1 \le \|(\mu - A)^{-1}\|\,\|E\|,
$$

the outer inequality of the chain (a2) of the Encyclopedia of Mathematics, *Bauer–Fike theorem*. Equivalently, every spectral value $\mu$ of $A + E$ outside the spectrum of $A$ satisfies $\|(\mu - A)^{-1}\|\,\|E\| \ge 1$: the spectrum of $A + E$ is contained in the union of the spectrum of $A$ and the set of $\mu \notin \sigma(A)$ with $\|(\mu - A)^{-1}\|\,\|E\| \ge 1$, a pseudospectrum of $A$. This product form is the one that gives the [Bauer–Fike theorem for diagonalizable matrices](exists-norm-sub-le-of-mem-spectrum-add.md). With $A$ the diagonal part of a matrix and the $\infty$-norm it gives only a weak, single-radius Gershgorin-type localisation: every eigenvalue lies within the largest off-diagonal row sum of some diagonal entry. The [stronger form](one-le-norm-inverse-mul-of-mem-spectrum.md) is needed for Gershgorin's theorem itself.

## Informally uses

- [Bauer–Fike exclusion theorem](one-le-norm-inverse-mul-of-mem-spectrum.md): combined with $\|(\mu - A)^{-1}E\| \le \|(\mu - A)^{-1}\|\,\|E\|$.
