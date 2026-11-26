# Envy graph and most envious agent of a partial allocation

For a partial allocation $X$ with monotone valuations, the envy graph $E_X$ is the directed graph on the agents with an arc $i \to j$ whenever $v_i(X_j) > v_i(X_i)$. For a set $S$ of goods that some agent envies, let $\kappa_X(S)$ be the smallest size of a subset $Z \subseteq S$ such that $v_k(Z) > v_k(X_k)$ for some agent $k$; agent $i$ is a most envious agent of $S$ if some $Z \subseteq S$ with $\lvert Z \rvert = \kappa_X(S)$ satisfies $v_i(Z) > v_i(X_i)$. For the set $P$ of unallocated goods, an agent $j$ champions a good $g \in P$ with respect to agent $i$ if $j$ is a most envious agent of $X_i \cup \{g\}$.

## Depends on

- [Partial EFX allocation with an unallocated pool](partial-efx-allocation-with-pool.md)
- [Envy cycle](../../../not-yet-classified/part-01/indivisible/is-envy-cycle.md)

## Sources

- B. R. Chaudhury, T. Kavitha, K. Mehlhorn, A. Sgouritsa, "A Little Charity Guarantees Almost Envy-Freeness", SODA 2020; SIAM Journal on Computing 50(4) (2021), arXiv:1907.04596.
- B. R. Chaudhury, J. Garg, K. Mehlhorn, "EFX Exists for Three Agents", EC 2020; Journal of the ACM 71(1) (2024), arXiv:2002.05119.
