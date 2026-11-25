# Sequential and parallel composition of pseudorandom generators

Let $G : S \to R \times S$ be a secure pseudorandom generator and let $n \ge 1$ be polynomially bounded in the security parameter. The $n$-wise sequential (Blum–Micali) composition, which computes $(r_1, s_1) = G(s_0)$, $(r_2, s_2) = G(s_1)$, and so on, and outputs $(r_1, \dots, r_n, s_n)$, is a secure pseudorandom generator from $S$ to $R^n \times S$; likewise the $n$-wise parallel composition $G'(s_1, \dots, s_n) = (G(s_1), \dots, G(s_n))$ is secure. In both cases, for every adversary $A$ there is an adversary $B$, running $A$ once plus at most $n$ evaluations of $G$, with $\mathrm{Adv}^{\mathrm{PRG}}[A, G'] = n \cdot \mathrm{Adv}^{\mathrm{PRG}}[B, G]$, where advantages are absolute differences of acceptance probabilities; the proof is a hybrid argument.

## Depends on

- [PRG advantage](prg-advantage.md)

## Proof depends on

- [The hybrid step](../../security-games/games-and-advantages/advantage-hybrid-uniform.md)

## Expansion

This page collects several results; it becomes ready once each is stated separately:

- Security of sequential (Blum–Micali) composition, as a page of its own
- Security of parallel composition, as a page of its own

## Sources

- D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, version 0.4, 2017, <https://toc.cryptobook.us/>, Theorems 3.2 and 3.3
