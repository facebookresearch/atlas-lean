# Distinct inversion and transposition actions on a circular genome

**Setting.** As in [the count of k-cut rearrangements of a circular genome](number-of-k-cut-rearrangements-of-a-circular-genome.md), a signed circular genome with $n$ oriented regions is a dihedral coset of signed permutations. Because both the genome and the reference circle have dihedral symmetry, the physical *action* of a rearrangement $\alpha$ is the double coset $\mathcal{D}_n\alpha\mathcal{D}_n$, encoded by the symmetric algebra element $\mathbf{z}\alpha\mathbf{z}$ with $\mathbf{z} = \frac{1}{2n}\sum_{d \in \mathcal{D}_n} d$ in the group algebra $\mathbb{C}[H_n]$. If $\mathbf{z}\alpha\mathbf{z} = \mathbf{z}\alpha'\mathbf{z}$ then the cut sets of $\alpha$ and $\alpha'$ are dihedrally related, so $|\mathrm{cuts}(\alpha)|$ is well defined on actions.

**Proposition.**
1. The number of distinct rearrangement actions applying exactly $2$ cuts (inversions) is $\lfloor n/2 \rfloor$.
2. The number of distinct rearrangement actions applying exactly $3$ cuts (signed transpositions) is

$$\left\lfloor \frac{n^2}{3} \right\rfloor - \left\lfloor \frac{n}{2} \right\rfloor.$$

## Depends on

- [Number of k-cut rearrangements of a circular genome](number-of-k-cut-rearrangements-of-a-circular-genome.md)

## Proof sketch

Up to rotation and reflection, two cuts are determined by the length of the shorter arc between them, which takes $\lfloor n/2 \rfloor$ values, and there is only one non-trivial way to rejoin two segments. Three cuts split the circle into three segments whose sizes form a partition of $n$ into three parts. Reassembling three unlabelled segments without restoring an adjacency gives $2$ distinct actions if all parts are equal, $3$ if exactly two are equal and $4$ if all differ; there are $\lfloor (n-1)/2 \rfloor$ partitions with exactly two equal parts and one with three equal parts exactly when $3 \mid n$. Summing over the partitions of $n$ into three parts with these weights gives $\lfloor n^2/3 \rfloor - \lfloor n/2 \rfloor$. These counts fix the number of distinct event types in a model-based (likelihood) distance for circular genomes when one restricts to inversions and transpositions.

## Sources

- Joshua Stevenson, Venta Terauds and Jeremy Sumner, "Rearrangement Events on Circular Genomes", *Bulletin of Mathematical Biology* 85 (2023), 107, <https://doi.org/10.1007/s11538-023-01209-5>. Preprint version: arXiv:2202.01968 (2022), Section 4.2 ("How many distinct $k$-cut rearrangement actions are there?"): the propositions counting 2-cut and 3-cut actions and the two counting lemmas on reassembling three segments and on partitions into three parts, <https://doi.org/10.48550/arXiv.2202.01968>.
