# Lower bound on the expected time to the most recent common ancestor of the seed-bank coalescent

Let $c, K \in (0, \infty)$ and, for the [seed-bank coalescent](seed-bank-coalescent-active-dormant-lineages.md) with seed-bank intensity $c$
and relative seed-bank size $1/K$, let $T_{\mathrm{MRCA}}[n]$ be the first time at which its
block-counting process, started from $n$ active and no dormant blocks, has one block left. Then

$$\liminf_{n \to \infty} \frac{\mathbb E\, T_{\mathrm{MRCA}}[n]}{\log \log n} > 0 .$$

## Depends on

- [Seed-bank coalescent: active/dormant lineages](seed-bank-coalescent-active-dormant-lineages.md)

## Expansion

A sound expansion follows the source proof. Couple the block counts with a process built from a
coloured seed-bank coalescent, in which an individual is coloured when its block leaves the seed bank,
so that the comparison process reaches one block no later than the seed-bank coalescent. The number
$A_n$ of blocks that enter the seed bank in the comparison process satisfies $A_n / \log n \to 2c$ in probability. Each of them
must leave the seed bank before the sample can have one ancestor, and they leave independently at rate
$cK$, so $T_{\mathrm{MRCA}}[n]$ is stochastically at least the extinction time of a pure death process
with per-individual rate $cK$ started from $A_n$, whose expectation grows like $\log A_n$.

## Sources

- J. Blath, A. González Casanova, N. Kurt and M. Wilke-Berenguer, "A new coalescent for seed-bank models", Annals of Applied Probability 26 (2016), 857–891, <https://doi.org/10.1214/15-AAP1106>, preprint <https://arxiv.org/abs/1411.4747>, Section 4, Definitions 4.2 and 4.5, Lemma 4.7 and Proposition 4.8 (the lower half of Theorem 4.6).
