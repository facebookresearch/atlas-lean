# Near-linear recognition of two-colored best match graphs

**Algorithm (Build2ColLRT).** Input: a connected properly 2-colored digraph $(\mathcal{G}=(L,E),\sigma)$ and a new root $\rho$.
1. Compute the umbrella vertices $U$, then $S^{(1)}=\{x\in U:N^-(x)\subseteq U\}$ and $S^{(2)}=\{x\in S^{(1)}:N^-(x)\subseteq S^{(1)}\}$.
2. If $S^{(1)}=\emptyset$ or $S^{(2)}\ne S^{(1)}$, reject.
3. Attach every $x\in S^{(2)}$ as a leaf child of $\rho$.
4. For each connected component $\mathcal{G}_v$ of $\mathcal{G}-S^{(2)}$: reject if it is a single vertex; otherwise create a child $v$ of $\rho$ and recurse on $\mathcal{G}_v$.

**Theorem.** For a connected properly 2-colored digraph, the algorithm returns a tree if and only if the input is a BMG, and the returned tree is then its unique least resolved tree. The LRT of a 2-colored BMG can be computed in $O(|V|+|E|\log^2|V|)$ time, by maintaining connected components under vertex deletions with a dynamic connectivity structure.

**Corollary.** Whether a properly 2-colored digraph is a binary-explainable BMG (equivalently, a BMG with no hourglass) can also be decided in $O(|V|+|E|\log^2|V|)$ time.

Disconnected inputs are handled componentwise, since a digraph is a BMG with a given color set if and only if each connected component is.

## Depends on

- [Support set of a two-colored best match graph](support-set-of-a-two-colored-best-match-graph.md)

## Expansion

Correctness follows from the support-set theorem: in a BMG the set computed in step 1 is exactly the leaf set attached to the LRT root, and two rounds of pruning suffice because in a BMG the pruning sequence stabilizes after one step, so a further change certifies a non-BMG. If the algorithm completes, the constructed tree is checked to explain the input by induction over the recursion. The naive implementation recomputes degrees on each component, giving quadratic time; the near-linear bound comes from maintaining the components with the Holm–de Lichtenberg–Thorup dynamic connectivity structure ($O(\log^2|V|)$ amortized per edge deletion) and keeping umbrella candidates in per-color lists indexed by out-degree. Binary explainability is then tested on the LRT by looking for a vertex with three children of the forbidden two-color pattern.

## Sources

- D. Schaller, M. Geiß, M. Hellmuth, P. F. Stadler, "Least resolved trees for two-colored best match graphs", arXiv:2101.07000 (2021), Algorithm 1, Theorems 5 and 6, Proposition 3, Corollary 4, Proposition 1, <https://doi.org/10.48550/arXiv.2101.07000>.
