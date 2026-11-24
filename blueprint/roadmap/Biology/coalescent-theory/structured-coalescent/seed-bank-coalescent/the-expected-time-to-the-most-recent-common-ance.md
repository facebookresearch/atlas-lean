# The expected time to the most recent common ancestor of the seed-bank coalescent is of order log log n

For $c, K \in (0, \infty)$, the time to the most recent common ancestor $T_{\mathrm{MRCA}}[n]$ of $n$
initially active lineages in the [seed-bank coalescent](seed-bank-coalescent-active-dormant-lineages.md) with seed-bank intensity $c$ and
relative seed-bank size $1/K$ satisfies $\mathbb E\, T_{\mathrm{MRCA}}[n] \asymp \log \log n$, that is,

$$0 < \liminf_{n \to \infty} \frac{\mathbb E\, T_{\mathrm{MRCA}}[n]}{\log \log n} \le \limsup_{n \to \infty} \frac{\mathbb E\, T_{\mathrm{MRCA}}[n]}{\log \log n} < \infty .$$

For comparison, in [Kingman's coalescent](../../kingman-s-coalescent-and-watterson-s-estimator/integral-tmrca.md) the expectation is
$2(1 - 1/n)$, bounded in $n$; the seed-bank coalescent also [does not come down from infinity](the-seed-bank-coalescent-does-not-come-down-from.md).

## Depends on

- [Seed-bank coalescent: active/dormant lineages](seed-bank-coalescent-active-dormant-lineages.md)

## Proof depends on

- [Lower bound on the expected time to the most recent common ancestor of the seed-bank coalescent](lower-bound-on-the-expected-time-to-the-most-rec.md)
- [Upper bound on the expected time to the most recent common ancestor of the seed-bank coalescent](upper-bound-on-the-expected-time-to-the-most-rec.md)

## Sources

- J. Blath, A. González Casanova, N. Kurt and M. Wilke-Berenguer, "A new coalescent for seed-bank models", Annals of Applied Probability 26 (2016), 857–891, <https://doi.org/10.1214/15-AAP1106>, preprint <https://arxiv.org/abs/1411.4747>, Section 4.2, Theorem 4.6, equations (4.13)–(4.15), proved in Propositions 4.8 and 4.12.
