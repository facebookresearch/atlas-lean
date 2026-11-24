# The seed-bank coalescent does not come down from infinity

Let $c, K \in (0, \infty)$ and consider the [seed-bank coalescent on $\mathbb N$](marked-active-dormant-seed-bank-coalescent-on-n.md) with
seed-bank intensity $c$ and relative seed-bank size $1/K$: active blocks merge pairwise at rate $1$, each
active block becomes dormant at rate $c$, each dormant block becomes active at rate $cK$, and dormant
blocks do not merge. Let $N_t$ and $M_t$ be its numbers of active and dormant blocks at time $t$, and
start it from infinitely many active and no dormant blocks, $(N_0, M_0) = (\infty, 0)$. Then

$$\mathbb P\bigl(M_t = \infty \text{ for all } t > 0\bigr) = 1 .$$

Consequently $N_t + M_t = \infty$ for every $t \ge 0$ almost surely, so the seed-bank coalescent does not
come down from infinity. The condition $t > 0$ is needed for the dormant count, since $M_0 = 0$.

## Depends on

- [Marked (active/dormant) seed-bank coalescent on N: projective extension](marked-active-dormant-seed-bank-coalescent-on-n.md)

## Expansion

A sound expansion follows the source proof: a coupling with a coloured seed-bank coalescent that marks
the lineages which have left the seed bank at least once; infinitely many lineages enter the seed bank
before any positive time, each stays dormant for an exponential time of rate $cK$, so $M_t = \infty$ with
probability one for each fixed $t > 0$, and monotonicity arguments upgrade this to all $t > 0$
simultaneously. The source's theorem is displayed for every starting configuration $(n, m)$ with $n + m$
infinite; its proof as written treats the start $(\infty, 0)$.

## Sources

- J. Blath, A. González Casanova, N. Kurt and M. Wilke-Berenguer, "A new coalescent for seed-bank models", Annals of Applied Probability 26 (2016), 857–891, <https://doi.org/10.1214/15-AAP1106>, preprint <https://arxiv.org/abs/1411.4747>, Section 4.1, Theorem 4.1 and its proof; Definitions 3.1 and 3.2 for the model and its rates.
