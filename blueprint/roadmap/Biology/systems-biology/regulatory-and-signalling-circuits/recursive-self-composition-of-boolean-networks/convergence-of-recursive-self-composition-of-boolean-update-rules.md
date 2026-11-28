# Convergence of recursive self-composition of Boolean update rules

**Setting.** A synchronous Boolean network on $n$ nodes is $\mathbf x(t+1) = \mathbf f(\mathbf x(t))$ with $\mathbf f : \{0,1\}^n \to \{0,1\}^n$. Its *recursive self-composites* are the logic functions $\mathbf f^p = \mathbf f \circ \dots \circ \mathbf f$ ($p$ times), regarded as elements of the finite set of maps $\{0,1\}^n \to \{0,1\}^n$. The *kernel states* are the states on attractors (fixed points and cycles) of the network.

**Theorem.**
1. *(Convergence.)* There are integers $0 \le p^* \le 2^n$ and $\ell^* \ge 1$ such that $\mathbf f^{p^* + r} = \mathbf f^{p^* + r + \ell^*}$ for all $r \ge 0$: the sequence of composites eventually enters a cycle of logics (a steady-state logic if $\ell^* = 1$, a cyclic logic otherwise), where $p^*$ is the first recursion at which the logic repeats.
2. *(Longest cycle.)* No attractor cycle of the network is longer than $\ell^*$.
3. *(Kernel states.)* For every fixed $r \ge 0$, the one-step image $\mathbf f^{p^* + r}(\mathbf x(0))$ ranges exactly over the kernel-state set of the original network.

## Expansion

The composites live in a finite semigroup, so the sequence $\mathbf f^p$ is eventually periodic: this is the index–period structure of a single element of a finite transformation semigroup. The index $p^*$ is the maximal transient length over all initial states (bounded by the number of states), and the period $\ell^*$ is the least common multiple of all attractor cycle lengths, since $\mathbf f^{p} = \mathbf f^{p+\ell}$ for $p \ge p^*$ exactly when $\mathbf f^{\ell}$ fixes every attractor state; hence item 2 (when cycles of coprime lengths coexist, $\ell^*$ exceeds every individual cycle length). After $p^*$ steps every state has reached its attractor, so the image of $\mathbf f^{p^*+r}$ is the set of attractor states, item 3. Computing the converged logic symbolically reveals repeated logical structure in update rules and finds all attractors without enumerating trajectories from every initial state.

## Sources

- J. Kim, W. Lee, K.-H. Cho, "Recursive Self-Composite Approach Towards Structural Understanding of Boolean Network", *IEEE/ACM Transactions on Computational Biology and Bioinformatics* 21(6) (2024), 1775–1783, Theorems 1, 2 and 3, <https://doi.org/10.1109/tcbb.2024.3415352> (preprint arXiv:2312.17344).
