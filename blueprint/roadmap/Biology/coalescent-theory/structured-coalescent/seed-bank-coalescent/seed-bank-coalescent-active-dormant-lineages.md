# Seed-bank coalescent

Let $c, K \in (0, \infty)$ and $k \ge 1$. A marked partition of $\{1, \dots, k\}$ is a partition together
with a flag $p$ (active) or $s$ (dormant) on each block. The seed-bank $k$-coalescent with seed-bank
intensity $c$ and relative seed-bank size $1/K$, started from a given marked partition, is the
[continuous-time Markov chain path process](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md) on marked partitions of $\{1, \dots, k\}$ whose
generator has the following off-diagonal rates, with diagonal entries minus the row sums:

- $\pi \mapsto \pi'$ at rate $1$ if $\pi'$ is obtained by merging two active blocks of $\pi$ into one
  active block;
- at rate $c$ if $\pi'$ is obtained by changing the flag of one block from $p$ to $s$;
- at rate $cK$ if $\pi'$ is obtained by changing the flag of one block from $s$ to $p$.

Dormant blocks do not merge. The source displays the definition for $k \ge 2$; the same rates extend it
to $k = 1$, where the single block switches from active to dormant at rate $c$ and back at rate $cK$. Its block-counting process $(N_t, M_t)$, the numbers of active and dormant
blocks, is the Markov chain with jumps $(n, m) \to (n - 1, m)$ at rate $\binom n2$,
$(n, m) \to (n - 1, m + 1)$ at rate $cn$ and $(n, m) \to (n + 1, m - 1)$ at rate $cKm$.

For two lineages started active, the expected time to their common ancestor is
$\bigl((1 + K)/K\bigr)^2$, independent of $c$: with $m_{aa}$, $m_{ad}$, $m_{dd}$ the expected times from
the states with both active, one active and one dormant, and both dormant, the first-step equations
$m_{aa} = \frac{1 + 2c\, m_{ad}}{1 + 2c}$, $m_{ad} = \frac{1 + c\, m_{dd} + cK m_{aa}}{c(1 + K)}$ and
$m_{dd} = \frac{1}{2cK} + m_{ad}$ give $m_{ad} = m_{aa} + \frac{2K + 1}{2cK^2}$ and
$m_{aa} = 1 + \frac{2K + 1}{K^2}$.

## Depends on

- [Path process of a finite continuous-time Markov chain](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-path.md)

## Expansion

A sound expansion also states that the family of seed-bank $k$-coalescents is consistent under
restriction and, as $c \to \infty$ with $K$ fixed, that the unmarked process converges to Kingman's
coalescent run at rate $(K/(1 + K))^2$, the probability that two lineages are both active in the
switching equilibrium; the second statement is not proved in the source.

## Sources

- J. Blath, A. González Casanova, N. Kurt and M. Wilke-Berenguer, "A new coalescent for seed-bank models", Annals of Applied Probability 26 (2016), 857–891, <https://doi.org/10.1214/15-AAP1106>, preprint <https://arxiv.org/abs/1411.4747>, Section 2, Definition 2.7 (block-counting process) and Section 3, Definition 3.1 (the seed-bank $k$-coalescent) and Remark 3.3.
