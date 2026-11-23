# A proper policy's Bellman operator is an |S|-stage contraction

Let $M$ be a Markov decision process with a finite set $S$ of nonterminal states, real rewards and [substochastic transitions](substochastic.md), and let $\mu$ be a [proper](proper.md) stationary policy. Then $T_\mu^{|S|}$, the $|S|$-th iterate of the undiscounted Bellman operator of $\mu$, is a contraction of $(S \to \mathbb{R}, \|\cdot\|_\infty)$: there is $K < 1$ with

$$\big\|T_\mu^{|S|} J - T_\mu^{|S|} J'\big\|_\infty \le K \|J - J'\|_\infty \quad \text{for all } J, J'.$$

The proof takes for $K$ the largest row sum $\rho_\mu$ of $P_\mu^{|S|}$, which is less than $1$ because $\mu$ is proper; when $S$ is empty, $\rho_\mu = 0$.

Bertsekas notes that $T_\mu$ is also a contraction for a suitable weighted sup norm.

## Sources

- D. P. Bertsekas, *Abstract Dynamic Programming*, 3rd ed., Athena Scientific (2022), Example 1.2.6 ("an $n$-stage contraction with respect to the unweighted sup-norm").

## Informally uses

- [Iterates of T_μ differ by powers of P_μ](policy-bellman-iterate-sub.md)
- [Powers of a substochastic matrix are substochastic](transition-matrix-pow-nonneg-and-sum-le.md)
