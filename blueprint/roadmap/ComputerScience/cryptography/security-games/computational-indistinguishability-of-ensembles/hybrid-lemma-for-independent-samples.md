# Hybrid lemma for polynomially many independent samples

Let $X$ and $Y$ be efficiently samplable distribution ensembles with $X \approx_c Y$, and let $t(n)$ be a polynomial computable from $1^n$. Then the ensembles of $t(n)$ independent samples,

$$X^{t}_n = (X_n^{(1)}, \dots, X_n^{(t(n))}) \quad\text{and}\quad Y^{t}_n = (Y_n^{(1)}, \dots, Y_n^{(t(n))}),$$

are computationally indistinguishable. Quantitatively, for every distinguisher $D$ for the $t$-fold product there is a distinguisher $D'$ for single samples, running in time that of $D$ plus $t(n)$ sampling costs, with $\mathrm{Adv}(D) \le t(n)\cdot \mathrm{Adv}(D')$.

## Proof sketch

Define hybrids $H_i$ whose first $i$ coordinates come from $Y$ and the rest from $X$. The distinguisher $D'$ picks $i$ uniformly, places its challenge at coordinate $i+1$, and samples the other coordinates itself; the telescoping sum of the hybrid gaps equals $t(n)$ times its advantage.

## Depends on

- [Computational indistinguishability of distribution ensembles](computational-indistinguishability-of-ensembles.md)
- [Samplable distributions](../../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/impagliazzo-s-five-worlds/samplable.md)

## Proof depends on

- [Hybrid argument](../games-and-advantages/advantage-le-sum.md)
- [The hybrid step](../games-and-advantages/advantage-hybrid-uniform.md)

## Sources

- O. Goldreich, "Foundations of Cryptography, Volume 1: Basic Tools", Cambridge University Press, 2001.
- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
