# The GGM construction: pseudorandom generators give pseudorandom functions

Let $G : S \to S \times S$ be a secure length-doubling pseudorandom generator and write $G(s) = (G_0(s), G_1(s))$. For $\ell \ge 1$ define $F : S \times \{0,1\}^\ell \to S$ by $F(k, x_1 \cdots x_\ell) = G_{x_\ell}(\cdots G_{x_2}(G_{x_1}(k)) \cdots)$. Then $F$ is a secure pseudorandom function: for every adversary $A$ making at most $Q$ queries there is an adversary $B$ of about the same running time with $\mathrm{Adv}^{\mathrm{PRF}}[A, F] \le \ell\, Q \cdot \mathrm{Adv}^{\mathrm{PRG}}[B, G]$.

## Depends on

- [PRG advantage](../pseudorandom-generators/prg-advantage.md)
- [PRF advantage](prf-advantage.md)

## Proof depends on

- [The hybrid step](../../security-games/games-and-advantages/advantage-hybrid-uniform.md)
- [Lazy random function](../../security-games/lazy-sampling-and-the-prp-prf-switching-lemma/lazy-rf.md)

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorem 4.10
- Original construction: O. Goldreich, S. Goldwasser and S. Micali, "How to construct random functions", *Journal of the ACM* 33(4):792–807, 1986. The statement above follows Boneh and Shoup, Theorem 4.10; the attribution follows Vadhan, *Pseudorandomness*, chapter notes to Chapter 7.
- S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science 7(1–3), 2012, chapter notes to Chapter 7
