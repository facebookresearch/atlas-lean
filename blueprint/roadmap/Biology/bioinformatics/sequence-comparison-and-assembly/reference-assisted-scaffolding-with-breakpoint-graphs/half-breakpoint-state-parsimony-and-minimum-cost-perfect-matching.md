# Half-breakpoint state parsimony and minimum-cost perfect matching

Let $BG(A, P_1, \dots, P_k)$ be the incomplete multi-colour breakpoint graph of an assembly $A$ and references $P_1, \dots, P_k$, and let $T$ be a rooted phylogeny with leaves $A, P_1, \dots, P_k$ and branch lengths $\tau$. Each vertex $u$ (a *half-breakpoint*) has, in genome $c$, a state $\mathrm{state}_c(u)$: the vertex joined to $u$ by the edge of colour $c$, or void if the block is absent from $c$.

**Half-breakpoint state parsimony.** Given the leaf states of $u$, label the internal nodes of $T$ with states so as to minimize

$$P(u, T) = \sum_{\text{branches } (i, j)} \bar\delta_{i,j}\, W(\tau_{ij}), \qquad W(\tau) = e^{-\tau}, \tag{1}$$

where $\bar\delta_{i,j} = 0$ if the states at the ends of the branch agree and $1$ otherwise. A Sankoff-type recursion solves it exactly: $s_t(\ell) = 0$ if leaf $\ell$ has state $t$ and $+\infty$ otherwise, and for an internal node $v$ with children $c$ joined by branches of length $\tau_c$,

$$s_t(v) = \sum_{c} \min_{t'} \big(s_{t'}(c) + \bar\delta_{t,t'}\, W(\tau_c)\big),$$

with optimum $\min_t s_t(\mathrm{root})$, in time $O(n d)$ for $n$ leaves and $d$ candidate states.

**Recovering adjacencies.** For each vertex $u$ without a red edge, and each candidate state $t$ (a vertex adjacent to $u$ in some reference), compute $P(u, T)$ with the target leaf fixed to state $t$. Give each candidate edge $\{u, t\}$ the weight $P(u, T \mid t) + P(t, T \mid u)$, remove the vertices already matched by red edges, and choose the missing red edges as a minimum-weight perfect matching of the remaining graph (blossom algorithm, $O(|V|^4)$ in the implementation). This choice minimizes the total half-breakpoint parsimony cost $\sum_u P(u, T)$ over all completions of the red matching that use candidate edges.

## Depends on

- [Incomplete multi-colour breakpoint graph](incomplete-multi-colour-breakpoint-graph.md)
- [Sankoff's algorithm](../../../phylogenetics/small-parsimony-problem/sankoff.md)

## Expansion

The cost $e^{-\tau}$ makes state changes cheaper on long branches, where rearrangements are more likely. Treating each half-breakpoint separately replaces the NP-hard problem of parsimony under 2-break (DCJ) operations by independent small-parsimony problems; each rearrangement touches at least two breakpoints, so this is an approximation, but a tractable one. Because choosing a red edge $\{u, t\}$ fixes the target states of both endpoints, the total cost of a completion is the sum of its edge weights, and the minimum-weight perfect matching gives the most parsimonious completion. Contigs are then chained along the inferred adjacencies; repeating at several synteny-block scales and merging consistent scaffolds, then filling gaps from the assembly graph, adds small and repetitive contigs.

## Sources

- M. Kolmogorov, B. Raney, B. Paten, S. Pham, "Ragout—a reference-assisted assembly tool for bacterial genomes", Bioinformatics 30(12) (2014) i302–i309, sections 2.2.2–2.2.5 and 2.3, Eq. (1), Algorithm 1, <https://doi.org/10.1093/bioinformatics/btu280> (PMC4058940).
