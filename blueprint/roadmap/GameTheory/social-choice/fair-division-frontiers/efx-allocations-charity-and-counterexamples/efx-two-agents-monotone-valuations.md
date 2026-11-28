# EFX exists for two agents with arbitrary monotone valuations

For every finite set of goods $M$ and every pair of monotone valuations $v_1, v_2 : 2^M \to \mathbb{R}_{\ge 0}$ there is a complete allocation that is EFX. Moreover, for any number $n$ of agents sharing one identical monotone valuation $v$, a complete EFX allocation exists.

## Proof sketch

For identical valuations, take a complete allocation that is leximin-optimal with respect to $v$, breaking ties to maximize bundle sizes lexicographically (leximin++); if some bundle $X_j$ minus a good were worth more than the poorest bundle, moving that good to the poorest agent would improve the leximin++ order. For two agents, agent $1$ computes such a partition for two copies of $v_1$, and agent $2$ chooses her preferred part; agent $1$ is EFX-satisfied by construction and agent $2$ is envy-free.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)

## Sources

- B. Plaut, T. Roughgarden, "Almost Envy-Freeness with General Valuations", SODA 2018; SIAM Journal on Discrete Mathematics 34(2) (2020).
