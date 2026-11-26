# EFX with bounded charity: fewer than n goods left unallocated

Let $n$ agents have monotone valuations on a finite set of goods $M$. There is a partial allocation $X$ with pool $P$ such that

1. $X$ is EFX;
2. no agent envies the pool: $v_i(X_i) \ge v_i(P)$ for every agent $i$;
3. $\lvert P \rvert < n$.

For additive valuations one can additionally guarantee that the Nash welfare of $X$ is at least half of the maximum Nash welfare over complete allocations.

## Proof sketch

Start from the empty allocation and repeatedly apply two update rules while maintaining EFX: rotate envy cycles, and, when some agent envies a subset of $P \cup X_j$ for a source-type configuration, give a most envious agent a minimal envied subset and return the rest to the pool. A potential function (the valuation vector compared lexicographically along a fixed ordering, together with the pool size) strictly improves at each step, so the process terminates. At termination every pool good is championed in a way that rules out $n$ or more goods remaining, because each agent can be the most envious agent of at most one pool good without an applicable update.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Envy graph and most envious agent of a partial allocation](envy-graph-most-envious-agent.md)

## Proof depends on

- [Envy-cycle rotation preserves EFX and weakly improves every agent](envy-cycle-rotation-preserves-efx.md)
- [Envy graph and most envious agent of a partial allocation](envy-graph-most-envious-agent.md)

## Sources

- B. R. Chaudhury, T. Kavitha, K. Mehlhorn, A. Sgouritsa, "A Little Charity Guarantees Almost Envy-Freeness", SODA 2020; SIAM Journal on Computing 50(4) (2021), arXiv:1907.04596.
