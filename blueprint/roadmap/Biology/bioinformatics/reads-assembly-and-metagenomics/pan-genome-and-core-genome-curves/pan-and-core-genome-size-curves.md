# Pan-genome and core-genome size curves

Let $\mathcal{G}$ be a finite set of $n$ genomes and $\mathcal{F}$ a finite set of gene families, with presence relation $G \ni F$ meaning that genome $G$ contains at least one member of family $F$. For each family let $m_F = \#\{G \in \mathcal G : G \ni F\} \in \{1,\dots,n\}$ (families absent from every genome are discarded). For a nonempty subset $A \subseteq \mathcal G$ define

$$\mathrm{pan}(A) = \#\{F : \exists G \in A,\ G \ni F\}, \qquad \mathrm{core}(A) = \#\{F : \forall G \in A,\ G \ni F\}.$$

Families with $m_F = n$ are **core**, with $1 < m_F < n$ **accessory**, and with $m_F = 1$ **unique**. For an ordering $G_1, \dots, G_n$ the pan- and core-genome curves are $k \mapsto \mathrm{pan}(\{G_1,\dots,G_k\})$ and $k \mapsto \mathrm{core}(\{G_1,\dots,G_k\})$.

**Proposition.**

1. Along any ordering, the pan curve is nondecreasing, the core curve is nonincreasing, and $\mathrm{core} \le \mathrm{pan}$ at every $k \ge 1$. The increment of the pan curve at step $k$ is the number of families in $G_k$ absent from $G_1,\dots,G_{k-1}$.
2. At $k = n$ the curves equal $|\mathcal F|$ and the number of core families, independently of the ordering.
3. If $A$ is a uniformly random $k$-subset of $\mathcal G$, then

$$\mathbb{E}\,\mathrm{pan}(A) = \sum_{F} \left(1 - \frac{\binom{n-m_F}{k}}{\binom{n}{k}}\right), \qquad \mathbb{E}\,\mathrm{core}(A) = \sum_F \frac{\binom{m_F}{k}}{\binom{n}{k}} .$$

In particular both expected curves depend on the data only through the gene family frequency spectrum $(\#\{F : m_F = j\})_{j=1}^n$.

## Remarks

Parts 1 and 2 are immediate from the definitions: adding a genome can only add families to a union and remove families from an intersection, and the intersection is contained in the union. For part 3, family $F$ is missed by $A$ exactly when $A$ is drawn from the $n - m_F$ genomes lacking it, and is core in $A$ exactly when $A$ is drawn from the $m_F$ genomes containing it; summing indicator expectations over families gives the formulas. Because a single ordering gives a noisy curve, pipelines such as BPGA average over random orderings, recording the median pan and core sizes at each $k$ (20 permutations by default); part 3 is the exact limit of the mean over all orderings.

## Sources

- N. M. Chaudhari, V. K. Gupta and C. Dutta, "BPGA: an ultra-fast pan-genome analysis pipeline", Scientific Reports 6 (2016) 24373, Methods ("Pan-genome profile analysis", pan/core indicator definitions, permutations; "Pan-genome sequence extraction", core/accessory/unique families), <https://doi.org/10.1038/srep24373>, PMCID PMC4829868.
