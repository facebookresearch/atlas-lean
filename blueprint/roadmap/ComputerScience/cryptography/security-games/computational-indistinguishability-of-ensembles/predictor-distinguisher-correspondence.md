# Next-bit predictors and distinguishers: exact transfer and the positional sum bound

Let $G : \{0,1\}^n \to \{0,1\}^{\ell}$ be a generator. (a) For every predictor $P$ for position $i$ there is a test $D_P$, which on input $y$ accepts iff $P(y_{1..i}) = y_{i+1}$, whose PRG advantage equals $|\mathrm{NBadv}_P(i)|$ exactly. (b) For every test $D$ there are predictors $P_0, \dots, P_{\ell-1}$, where $P_i$ completes the prefix $y_{1..i}$ with uniform bits $r_{i+1}, \dots, r_\ell$, runs $D$ and outputs $r_{i+1}$ if $D$ accepts and $1 - r_{i+1}$ otherwise, such that

$$\mathrm{PRGadv}(D, G) = \Bigl|\sum_{i=0}^{\ell-1} \mathrm{NBadv}_{P_i}(i)\Bigr| \le \sum_{i=0}^{\ell-1} |\mathrm{NBadv}_{P_i}(i)|.$$

## Proof sketch

Part (a) is a direct computation, using that a uniform bit is guessed with probability exactly $1/2$. For (b), let $H_i$ be the distribution whose first $i$ bits come from $G(s)$ and whose remaining bits are uniform; then $H_0$ is uniform, $H_\ell = G(U_n)$, and the gap $\Pr[D(H_{i+1})=1] - \Pr[D(H_i)=1]$ equals the advantage of $P_i$.

## Depends on

- [Next-bit unpredictability of a generator](next-bit-unpredictability.md)
- [PRG advantage](../../symmetric-key/pseudorandom-generators/prg-advantage.md)

## Proof depends on

- [Hybrid argument](../games-and-advantages/advantage-le-sum.md)

## Sources

- D. Boneh and V. Shoup, "A Graduate Course in Applied Cryptography", draft textbook, version 0.6, 2023.
- A. C. Yao, "Theory and Application of Trapdoor Functions", Proceedings of the 23rd Annual IEEE Symposium on Foundations of Computer Science (FOCS), 1982.
