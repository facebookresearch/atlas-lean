# k-mer size selection score for assembly graphs

**Setting.** For each candidate $k$ in a finite set $K$ (ten values spanning 20–95% of the read length, capped at 127, in the source), a de Bruijn assembly graph $G_k$ is built. Let $c_k \ge 1$ be its number of contigs and $d_k \ge 0$ its number of dead ends (contig ends with no outgoing connection).

**Definition.** The graph score is

$$\mathrm{score}(G_k) = \frac{1}{c_k\,(d_k + 1)^2},$$

and the selected graph is $G_{k^\ast}$ with $k^\ast \in \operatorname*{arg\,max}_{k \in K} \mathrm{score}(G_k)$.

**Proposition.** The score is strictly decreasing in $c_k$ for fixed $d_k$ and in $d_k$ for fixed $c_k$. One additional dead end, from $d$ to $d + 1$, is offset only by reducing the contig count by the factor $\big((d+1)/(d+2)\big)^2$; in particular, a graph with $c$ contigs and no dead ends scores strictly higher than a graph with $c'$ contigs and one dead end when $c' > c/4$, scores the same when $c' = c/4$ (for example $c = 4$, $c' = 1$, both scoring $1/4$), and scores strictly lower when $c' < c/4$.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Remarks

Larger $k$ resolves more repeats and yields fewer, longer contigs, but past a point coverage gaps break the graph and create dead ends. The score trades the two off, with the squared factor penalizing dead ends more heavily because later bridging and multiplicity steps depend on graph connectivity; the $+1$ keeps the score finite for complete graphs. After selection the source removes contigs whose depth is below half the median graph depth unless doing so would create a dead end, which filters low-level contamination.

## Sources

- R. R. Wick, L. M. Judd, C. L. Gorrie and K. E. Holt, *Unicycler: Resolving bacterial genome assemblies from short and long sequencing reads*, PLoS Comput. Biol. 13 (2017), e1005595. <https://doi.org/10.1371/journal.pcbi.1005595> (PMCID: PMC5481147). Design and implementation, "Short-read assembly".
