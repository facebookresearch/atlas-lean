# Closed-form fusion, fission and block-interchange distance

**Genomes as permutations.** A genome with $n$ distinct genes $E = \{1, \dots, n\}$ on circular chromosomes is the permutation $\alpha$ of $E$ whose cycles are the chromosomes, each listing its genes in cyclic order. Let $\chi(\alpha)$ be the number of chromosomes and $f(\alpha)$ the number of cycles of $\alpha$ counting fixed points. Composing with a 2-cycle $(x\,y)$ either joins two cycles into one (a **fusion** of two chromosomes) or splits one cycle into two (a **fission**), and a **block-interchange** (swapping two non-overlapping blocks within one chromosome) is a product of two 2-cycles acting within a single cycle. For target genome $I$ on the same genes, $d(\alpha, I)$ is the minimum number of fusions, fissions and block-interchanges transforming $\alpha$ into $I$; it is symmetric.

**Lemma (transposition lower bound).** If $\alpha = \alpha_1 \cdots \alpha_m$ with every $\alpha_i$ a 2-cycle, then $m \ge n - f(\alpha)$.

**Canonical order.** Some optimal scenario performs all fusions first, then all block-interchanges, then all fissions. If the bipartite graph $G(\alpha, I)$ joining a chromosome of $\alpha$ to a chromosome of $I$ whenever they share a gene is connected, an optimal scenario uses

$$n_{fu} = \chi(\alpha) - 1, \qquad n_{fi} = \chi(I) - 1, \qquad n_{bi} = \frac{n - f(I\alpha^{-1}) - n_{fu} - n_{fi}}{2}$$

fusions, fissions and block-interchanges respectively.

**Theorem.** Let $G(\alpha, I)$ have $\omega$ connected components. Then

$$d(\alpha, I) = \frac{n - f(I\alpha^{-1}) + \chi(\alpha) + \chi(I)}{2} - \omega,$$

and an optimal scenario in canonical order can be computed in $O(n^2)$ time.

## Expansion

Any scenario is a product of 2-cycles equal to $I\alpha^{-1}$, fusions and fissions contributing one each and block-interchanges two, so the lemma bounds the event count from below by $n - f(I\alpha^{-1})$ weighted accordingly. Fusions and fissions are each forced in number within a component (every chromosome of $\alpha$ in the component must be merged into one and then split into the chromosomes of $I$), and choosing the fusion transpositions inside cycles of $I\alpha^{-1}$ keeps the count tight, leaving the block-interchanges to account for the remaining transpositions in pairs. Summing the per-component counts $\delta_i = n_{fu} + n_{bi} + n_{fi}$ gives the formula. The method was used to compare gene orders of multi-chromosomal circular bacterial genomes.

## Sources

- C. L. Lu, Y. L. Huang, T. C. Wang, H.-T. Chiu, "Analysis of circular genome rearrangement by fusions, fissions and block-interchanges", BMC Bioinformatics 7:295 (2006), Lemmas 1–7 and Theorem 1 (Algorithm Sorting-by-ffbi), <https://doi.org/10.1186/1471-2105-7-295>, PMCID PMC1569878.
