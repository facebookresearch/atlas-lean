# APX-hardness of the family-free DCJ distance

**Setting.** Genomes $A$ and $B$ are sets of linear or circular chromosomes over genes $\mathcal A$ and $\mathcal B$, with a normalized similarity $\sigma : \mathcal A \times \mathcal B \to [0,1]$. The *gene similarity graph* $GS_\sigma(A,B)$ is the bipartite graph on $\mathcal A \cup \mathcal B$ with an edge of weight $\sigma(a,b)$ whenever $\sigma(a,b) > 0$. A matching $M$ in it, with weight $w(M) = \sum_{e \in M}\sigma(e)$, induces *reduced genomes* $A^M, B^M$ in which each matched pair becomes one common gene and unmatched genes are deleted. In the weighted adjacency graph $AG_\sigma(A^M, B^M)$, each component $C$ (with $|C|$ its number of edges and $w(C)$ its total weight) contributes

$$d_\sigma(C) = \begin{cases} \frac{2|C| - w(C)}{2} - 1, & C \text{ a cycle},\\ \frac{2|C| - w(C) - 1}{2}, & C \text{ an odd path},\\ \frac{2|C| - w(C)}{2}, & C \text{ an even path},\end{cases}$$

and summing gives

$$d_\sigma(A^M, B^M) = d_{\mathrm{DCJ}}(A^M, B^M) + |M| - w(M),$$

with $d_{\mathrm{DCJ}}$ the [double-cut-and-join distance](../../genome-rearrangements/double-cut-and-join-distance-formula.md) of the reduced genomes. Because the empty matching gives distance $0$, the *family-free DCJ distance* minimizes over maximal matchings $\mathbb M$:

$$d_{\mathrm{FFDCJ}}(A, B) = \min_{M \in \mathbb M} d_\sigma(A^M, B^M).$$

**Theorem.** Computing $d_{\mathrm{FFDCJ}}(A,B)$ is APX-hard, even when every gene of $A$ has degree at most one and every gene of $B$ degree at most two in $GS_\sigma(A,B)$. Consequently no polynomial-time algorithm approximates it within a factor better than $1237/1236$ unless P = NP. The companion family-free DCJ similarity, maximized over maximal matchings, is NP-hard under the same degree restriction.

## Depends on

- [Double-cut-and-join distance formula](../../genome-rearrangements/double-cut-and-join-distance-formula.md)

## Expansion

The proof is an approximation-preserving (AP) reduction from the exemplar DCJ distance problem in which each gene family occurs once in one genome and at most twice in the other, itself hard to approximate within $1237/1236 - \epsilon$. Families become genes with similarity $1$ between all copies; a maximal matching then chooses one copy of each duplicated family, exactly an exemplar choice, and with all weights equal to $1$ the correction term $|M| - w(M)$ vanishes so $d_\sigma$ equals the DCJ distance of the exemplar genomes. The source also gives an integer linear program solving the problem exactly.

## Sources

- F. V. Martinez, P. Feijão, M. D. V. Braga and J. Stoye, "On the family-free DCJ distance and similarity", *Algorithms for Molecular Biology* (2015), Eqs. (1)–(2), Theorem 1, Corollary 2 and Theorem 3. <https://doi.org/10.1186/s13015-015-0041-9> (PMC4391664)
