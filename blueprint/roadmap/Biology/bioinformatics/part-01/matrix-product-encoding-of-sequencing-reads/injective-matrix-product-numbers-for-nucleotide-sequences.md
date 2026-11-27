# Injective matrix-product numbers for nucleotide sequences

**Encoding.** A read of length $l$ over $\{A,C,G,T\}$ (possibly with masked positions $N$) is split into four binary strings $B^{(x)} = b_1\cdots b_l$, $x \in \{A,C,G,T\}$, with $b_j = 1$ iff position $j$ is nucleotide $x$. With

$$M_0 = \begin{pmatrix}1 & 0\\ 1 & 1\end{pmatrix}, \qquad M_1 = \begin{pmatrix}1 & 1\\ 0 & 1\end{pmatrix} = M_0^{\mathsf T},$$

a binary string $B$ is mapped to $M_B = M_{b_1}M_{b_2}\cdots M_{b_l}$, and to the number $\log\operatorname{tr}(WM_B)$ for a weight matrix $W$ whose four entries are $1, \sqrt2, \sqrt3, \sqrt5$. The read is represented by the quadruplet of these numbers over $x \in \{A,C,G,T\}$.

**Proposition 1.** Distinct binary strings give distinct product matrices: $B \mapsto M_B$ is injective.

**Proposition 2.** For integer matrices $F, G$, $\operatorname{tr}(WF) = \operatorname{tr}(WG)$ if and only if $F = G$.

**Corollary.** Two reads of the same length have the same quadruplet if and only if they are identical. Hence binning reads by distinct quadruplets reproduces exact $k$-mer counting ($k = l$), while nearby quadruplets correspond to similar reads, so histogram estimates of the four-dimensional quadruplet distribution and the Hellinger distance between samples interpolate between exact matching and similarity.

## Depends on

- [Hellinger distance](../../../../Probability/convergence-of-measures/hellinger-distance/hellinger-dist.md)

## Expansion

Right multiplication by $M_0$ adds the second column of a matrix to the first, and by $M_1$ adds the first column to the second; since entries stay positive, the last letter is recovered by seeing which column dominates entrywise, subtracting, and repeating, which inverts the map (the two matrices generate a free monoid inside $SL_2(\mathbb Z)$). For Proposition 2, $\operatorname{tr}(WF) = \sum_{i,j}W_{ij}F_{ji}$ is a rational combination of $1,\sqrt2,\sqrt3,\sqrt5$, and square roots of distinct square-free integers are linearly independent over $\mathbb Q$, so the combination determines all four integer entries. Small edits change only a few factors of the product, which keeps the numbers of similar reads close (alternating strings give Fibonacci entries, showing exponential growth and hence the logarithm). Including each read's reverse complement removes strand bias, and regressing quadruplets on GC content removes amplification bias before distances are computed.

## Sources

- H. Dai, Y. Guan, "The Nubeam reference-free approach to analyze metagenomic sequencing reads", Genome Research 30(9) (2020) 1364–1375, Results (Nubeam; Nubeam includes the k-mer method as a special case), Propositions 1–2, <https://doi.org/10.1101/gr.261750.120>, PMCID PMC7545149.
