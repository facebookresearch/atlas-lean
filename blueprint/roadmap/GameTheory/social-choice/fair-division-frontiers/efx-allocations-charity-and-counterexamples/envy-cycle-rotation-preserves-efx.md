# Envy-cycle rotation preserves EFX and weakly improves every agent

Let $X$ be a partial EFX allocation for monotone valuations, and let $i_1 \to i_2 \to \dots \to i_k \to i_1$ be a directed cycle in its envy graph. Let $X'$ be obtained by giving each $i_\ell$ the bundle $X_{i_{\ell+1}}$ (indices modulo $k$), keeping all other bundles and the pool. Then $X'$ is a partial EFX allocation, $v_i(X'_i) \ge v_i(X_i)$ for every agent $i$ with strict inequality on the cycle, and the multiset of bundles is unchanged. Consequently a partial EFX allocation whose envy graph is acyclic can always be reached without decreasing any agent's value.

## Proof sketch

EFX is a condition comparing each agent's own value with her values of the other bundles minus a good; since the family of bundles is unchanged and each agent's own value weakly increases, every EFX inequality persists. Each rotation strictly increases $\sum_i v_i(X_i)$ over a finite set of allocations of the same bundles, so repeated rotation terminates with an acyclic envy graph.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Envy graph and most envious agent of a partial allocation](envy-graph-most-envious-agent.md)

## Sources

- R. J. Lipton, E. Markakis, E. Mossel, A. Saberi, "On approximately fair allocations of indivisible goods", EC 2004.
- B. R. Chaudhury, T. Kavitha, K. Mehlhorn, A. Sgouritsa, "A Little Charity Guarantees Almost Envy-Freeness", SODA 2020; SIAM Journal on Computing 50(4) (2021), arXiv:1907.04596.
