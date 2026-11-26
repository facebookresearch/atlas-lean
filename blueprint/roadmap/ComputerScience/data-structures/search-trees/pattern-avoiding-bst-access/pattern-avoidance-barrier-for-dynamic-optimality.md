# Pattern avoidance as a barrier for dynamic optimality

If an online BST algorithm $\mathcal{A}$ is dynamically optimal, then for every fixed $\pi$ there is a constant $c'_\pi$ with $\mathrm{cost}_{\mathcal{A}}(X) \le c'_\pi\, n$ for every $\pi$-avoiding permutation access sequence $X \in S_n$. In particular a proof that splay trees or Greedy are dynamically optimal must in passing establish $O(1)$ amortized cost on all pattern-avoiding inputs, which current analyses achieve only up to superconstant inverse-Ackermann factors.

## Proof sketch

Combine $\mathrm{cost}_{\mathcal{A}}(X) \le c\,\mathrm{OPT}(X)$ with $\mathrm{OPT}(X) \le c_\pi n$ from the linear optimal cost of pattern-avoiding inputs.

## Depends on

- [Pattern-avoiding inputs have linear optimal BST cost](optimal-bst-cost-on-pattern-avoiding-inputs.md)
- [Dynamic optimality](../dynamic-optimality/dynamic-optimality.md)

## Proof depends on

- [Pattern-avoiding inputs have linear optimal BST cost](optimal-bst-cost-on-pattern-avoiding-inputs.md)
- [Dynamic optimality](../dynamic-optimality/dynamic-optimality.md)

## Sources

- Benjamin Aram Berendsohn, László Kozma, Michal Opler, "Optimization with Pattern-Avoiding Input", STOC (2024), arXiv:2310.04236.
