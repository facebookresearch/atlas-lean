# Fixed-parameter tractable counting of single cut-and-join scenarios

**Setting.** A genome is a set of oriented genes (edges) whose extremities are joined into *adjacencies* (two extremities) or left as *telomeres* (one extremity); it is determined by its sets of adjacencies and telomeres. In the *Single Cut-and-Join* (SCaJ) model the allowed operations are
1. *cut*: an adjacency $ab$ becomes two telomeres $a,b$;
2. *join*: two telomeres $a,b$ become an adjacency $ab$;
3. *cut-join*: adjacency $ab$ and telomere $c$ become adjacency $ac$ and telomere $b$

(double-cut-join is not allowed). For genomes $G_1,G_2$ on the same genes, a *scenario* is a sequence of operations turning $G_1$ into $G_2$; the *distance* is the minimum length, and a scenario of that length is *most parsimonious*. **Pairwise Rearrangement** asks for the number of most parsimonious scenarios. The *adjacency graph* of $(G_1,G_2)$ has the adjacencies and telomeres of both genomes as vertices, joined when they share an extremity; its components are cycles and paths, and a component is *trivial* if it is a cycle of length $2$ (an adjacency shared by both genomes) or a path of length $1$ (a shared telomere).

**Theorem.** In the SCaJ model, Pairwise Rearrangement (counting most parsimonious scenarios) is fixed-parameter tractable in the number of nontrivial components of the adjacency graph. Since every nontrivial component contributes at least one to the distance, it is also fixed-parameter tractable in the distance $d(G_1,G_2)$.

**Combinatorial core.** Components are classified as crowns (cycles) and as $W$-, $M$- and $N$-shaped paths according to how their endpoints alternate between the two genomes. A set of components can be sorted jointly by interleaved operations iff it avoids four obstructions: two or more components one of which is a trivial crown; two $W$-shaped components; two $M$-shaped components; or more than one path together with an $N$-shaped component. The number of joint sorting sequences for admissible sets obeys explicit recurrences in the component sizes, and the total count sums these over the ways operations can merge components, which is exponential only in the number of nontrivial components.

## Expansion

Counting is $\#\mathsf P$-complete in this model, so exact uniform sampling of scenarios is intractable in general. The obstruction comes from operations that act across components; once the number of nontrivial components is bounded, all ways that sorting operations can couple them can be enumerated, while the trivial components contribute nothing. The result identifies the number of nontrivial components as the parameter controlling hardness of sampling rearrangement histories.

## Sources

- Lora Bailey, Heather Smith Blake, Garner Cochran, Nathan Fox, Michael Levet, Reem Mahmoud, Inne Singgih, Grace Stadnyk and Alexander Wiedemann, "Pairwise Rearrangement is Fixed-Parameter Tractable in the Single Cut-and-Join Model", arXiv:2402.01942 (2024), Theorem 1.1, Corollary 1.2, Section 2 (operations and adjacency graph), Proposition 3.2, Theorem 3.3 and Propositions 3.5–3.6, <https://doi.org/10.48550/arXiv.2402.01942>.
