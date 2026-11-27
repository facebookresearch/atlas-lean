# EFX with bounded charity: fewer than n goods left unallocated

Let $n$ agents have monotone valuations with $v_i(\emptyset) = 0$ on a finite set of goods $M$. There is a partial allocation $X$ with pool $P$ such that

1. $X$ is EFX;
2. no agent envies the pool: $v_i(X_i) \ge v_i(P)$ for every agent $i$;
3. $\lvert P \rvert < n$.

For additive valuations one can additionally guarantee $v_i(X_i) \ge \tfrac12 v_i(X^*_i)$ for every agent $i$, where $X^*$ is a maximum Nash welfare allocation of $M$; in particular the Nash welfare of $X$ is at least half of the maximum.

## Proof sketch

Start from the empty allocation and apply three update rules while keeping EFX and an acyclic envy graph: give a pool good to a source of the envy graph when this keeps EFX (the pool shrinks and no value drops); give an agent who envies the pool a minimal envied subset of it, returning her bundle to the pool; and, when there are distinct pool goods $g_0, \dots, g_{\ell-1}$, distinct sources $s_0, \dots, s_{\ell-1}$ and distinct agents $t_1, \dots, t_\ell$ with $t_i$ a most envious agent of $X_{s_{i-1}} \cup \{g_{i-1}\}$ and reachable from $s_i$, give each $t_i$ a minimal envied subset of $X_{s_{i-1}} \cup \{g_{i-1}\}$ and shift bundles along the envy paths. The last two rules strictly increase the social welfare $\sum_i v_i(X_i)$ and the first shrinks the pool without lowering it, so the process terminates. If the first rule does not apply and $\lvert P \rvert \ge n$, a chain of such triples can always be built, so at termination $\lvert P \rvert < n$ and nobody envies the pool. For the Nash welfare bound, start from an allocation derived from a maximum Nash welfare allocation instead of the empty one.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Envy graph and most envious agent of a partial allocation](envy-graph-most-envious-agent.md)
- [Nash Welfare](../../../not-yet-classified/part-01/indivisible/nash-welfare.md)

## Proof depends on

- [Envy-cycle rotation preserves EFX and weakly improves every agent](envy-cycle-rotation-preserves-efx.md)

## Sources

- B. R. Chaudhury, T. Kavitha, K. Mehlhorn, A. Sgouritsa, "A Little Charity Guarantees Almost Envy-Freeness", SODA 2020; SIAM Journal on Computing 50(4) (2021), arXiv:1907.04596.
