# Pattern avoidance as a barrier for dynamic optimality

If an online BST algorithm $\mathcal{A}$ is dynamically optimal, then for every fixed $\pi$ there is a constant $c'_\pi$ with $\mathrm{cost}_{\mathcal{A}}(X) \le c'_\pi\, n$ for every $\pi$-avoiding permutation access sequence $X \in S_n$. In particular a proof that splay trees or Greedy are dynamically optimal must in passing establish $O(1)$ amortized cost on all pattern-avoiding inputs, which current analyses do not reach: for Greedy the best bounds carry superconstant inverse-Ackermann-type factors, and for splay trees nothing better than the trivial $O(n \log n)$ is known apart from special cases such as sequential access.

## Proof sketch

Combine $\mathrm{cost}_{\mathcal{A}}(X) \le c\,\mathrm{OPT}(X)$ with $\mathrm{OPT}(X) \le c_\pi n$ from the linear optimal cost of pattern-avoiding inputs.

## Depends on

- [Dynamic optimality](../dynamic-optimality/dynamic-optimality.md)
- [Classical pattern containment in a sequence](../../../../Combinatorics/permutations/permutation-patterns/cyclic-pattern-avoiding-stack-sorting/contains-pattern-seq.md)

## Proof depends on

- [Pattern-avoiding inputs have linear optimal BST cost](optimal-bst-cost-on-pattern-avoiding-inputs.md)

## Sources

- Benjamin Aram Berendsohn, László Kozma, Michal Opler, "Optimization with Pattern-Avoiding Input", STOC (2024), arXiv:2310.04236.
