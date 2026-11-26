# Computational indistinguishability of distribution ensembles

A *distribution ensemble* is a sequence $X = (X_n)_{n \in \mathbb{N}}$ of probability distributions on finite bit strings, indexed by the security parameter $n$. Two ensembles $X$ and $Y$ are *computationally indistinguishable*, written $X \approx_c Y$, if for every probabilistic polynomial-time distinguisher $D$ that receives $1^n$ and a sample $w$ and outputs a bit, the function

$$\varepsilon_D(n) = \left| \Pr_{w \leftarrow X_n}[D(1^n, w) = 1] - \Pr_{w \leftarrow Y_n}[D(1^n, w) = 1] \right|$$

is negligible in $n$. The relation is reflexive and symmetric, and it is transitive along any fixed finite chain of ensembles by the triangle inequality for advantages. Neither ensemble is required to be efficiently samplable.

## Depends on

- [Probabilistic polynomial-time Turing machines](../asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Negligible functions](../../../../TheoryOfComputation/complexity-classes/time-and-space-complexity-classes/negligible.md)
- [Distinguishing advantage](../games-and-advantages/advantage.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
