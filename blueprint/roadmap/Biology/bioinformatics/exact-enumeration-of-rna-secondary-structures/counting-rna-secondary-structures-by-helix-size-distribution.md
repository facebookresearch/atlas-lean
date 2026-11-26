# Counting RNA secondary structures by helix size distribution

**Setting.** Use RNA secondary structures, base pairs, isolated bases, partial stacks and loops as in [Counting RNA secondary structures by partial stacks and loop sizes](counting-rna-secondary-structures-by-partial-stacks-and-loop-sizes.md). A *helix* is a maximal set of mutually nested arcs with no isolated base between an arc and the arc directly inside it, so both its left ends and its right ends are consecutive; its size is its number of arcs. A helix size distribution $1^{a_1}2^{a_2}\cdots(b+1)^{a_{b+1}}$ means $a_i$ helices of size $i$, with $\sum_i ia_i=b+1$ base pairs and $\sum_i a_i=s$ helices; a loop size distribution $1^{c_1}2^{c_2}\cdots$ similarly has $\sum_i ic_i=b+k$, and $l_o=\sum_{i>1}c_i$.

**Theorem.** Let $k>1$.

1. The number of structures with $b+1$ base pairs, $k$ isolated bases, $s$ helices of size distribution $(a_i)$ and loops of size distribution $(c_i)$ is

$$\frac{s!}{\prod_{i}a_i!}\,\frac{(l_o-1)!}{\prod_{i>1}c_i!}\binom{k-1+l_o}{s-1}\binom{s-1}{l_o-1},$$

and refining further by the number $l_e$ of partial stacks the count is $\frac{s!}{\prod a_i!}\frac{(l_o-1)!}{\prod_{i>1}c_i!}\binom{k-1}{l_e-1}\binom{s-1}{l_o-1}\binom{l_o}{l_e+l_o-s}$.

2. The number with $s$ helices of size distribution $(a_i)$ is

$$\frac{s!}{a_1!\cdots a_{b+1}!}\,\frac{1}{k-1}\sum_{l_o=1}^{s}\binom{k-1}{l_o}\binom{s-1}{l_o-1}\binom{k-1+l_o}{s-1}.$$

3. The number with $s$ helices each of size at least $\sigma$ is

$$\binom{b-(\sigma-1)s}{s-1}\,\frac{1}{k-1}\sum_{l_o=1}^{s}\binom{k-1}{l_o}\binom{s-1}{l_o-1}\binom{k-1+l_o}{s-1}.$$

4. Consequently, for a uniformly random structure with $b+1$ base pairs, $k$ isolated bases and $s$ helices all of size at least $\sigma$, the helix sizes, read in order, form a uniformly random composition of $b+1$ into $s$ parts of size at least $\sigma$, so

$$\Pr\big[\text{helix sizes }1^{a_1}\cdots(b+1)^{a_{b+1}}\big]=\frac{s!\,(s-1)!\,(b-\sigma s+1)!}{a_1!\cdots a_{b+1}!\,(b-\sigma s+s)!},\qquad a_i=0\text{ for }i<\sigma.$$

These are exact versions of asymptotic helix and loop statistics of Hofacker, Schuster and Stadler.

## Expansion

Under Chen's bijection to set-alternating plane trees, helices correspond to *E-blocks* (maximal groups of even-level vertices forming a helix) and their sizes to block sizes. A variation of Chen's bijective method for counting trees by forests of small trees maps these trees, with given numbers of E-blocks, even-level and odd-level internal vertices, to forests of small set-alternating trees over enlarged label sets. Forests of small trees are counted by direct products of multinomials, which gives the closed product formulas. Because the helix sizes enter only through the multinomial factor $s!/\prod a_i!$, conditioning on $s$ makes the helix composition a uniformly random composition, which is the source of the explicit probability in part 4.

## Depends on

- [Counting RNA secondary structures by partial stacks and loop sizes](counting-rna-secondary-structures-by-partial-stacks-and-loop-sizes.md)

## Sources

- Ricky X. F. Chen, Christian M. Reidys, Michael S. Waterman, "Exact enumeration of RNA secondary structures by helices and loops", arXiv:2407.06220 (2024): Section 3.2 (proposition relating helices to E-blocks, bijection theorem to forests of small trees, joint distribution theorem and corollary), Section 3.3 (enumeration by helices: size-distribution theorem, minimum helix size count and the probability corollary). <https://doi.org/10.48550/arXiv.2407.06220>
