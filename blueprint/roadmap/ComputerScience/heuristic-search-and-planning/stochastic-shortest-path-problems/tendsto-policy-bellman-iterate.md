# Value iteration for a proper policy converges

Let $M$ be a Markov decision process with a finite set $S$ of nonterminal states, real rewards and substochastic transitions, and let $\mu$ be a proper stationary policy. For every $J : S \to \mathbb{R}$, the iterates $T_\mu^k J$ of the undiscounted Bellman operator of $\mu$ converge, as $k \to \infty$, to the [value](ssp-value.md) of $\mu$.

When $S$ is empty there is only one function $S \to \mathbb{R}$, and the statement is trivial. Otherwise, writing $k = q|S| + r$ with $0 \le r < |S|$, the distance from $T_\mu^k J$ to the fixed point is at most $\rho_\mu^{\,q} \|J - J_\mu\|_\infty$, because $T_\mu^{|S|}$ contracts by $\rho_\mu$ and $T_\mu$ does not expand distances.

## Sources

- D. P. Bertsekas, *Abstract Dynamic Programming*, 3rd ed., Athena Scientific (2022), Example 1.2.6 ($J_\mu = \lim_k T_\mu^k J$ for every $J$).

## Informally uses

- [A proper policy's Bellman operator is an |S|-stage contraction](contracting-with-policy-bellman-iterate.md)
