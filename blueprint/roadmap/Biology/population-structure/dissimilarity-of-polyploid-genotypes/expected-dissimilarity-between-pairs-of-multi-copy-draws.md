# Expected dissimilarity between pairs of multi-copy draws from two allele-frequency vectors

**Setting.** Let $I \ge 2$ objects (e.g. alleles) have probability vectors $\mathbf{p}, \mathbf{q}$ on $\{1,\dots,I\}$. Draw $K \ge 2$ items with replacement according to $\mathbf{p}$, and independently $K$ items according to $\mathbf{q}$, recording each draw as an unordered multiset, i.e. a count vector $\mathbf{g} \in \mathbb{Z}_{\ge 0}^I$ with $\sum_i g^{(i)} = K$ (a $K$-ploid genotype at a locus with $I$ alleles). The dissimilarity of two draws is

$$\mathcal{D}(\mathbf{g}_1, \mathbf{g}_2) = 1 - \frac{1}{K^2}\sum_{1 \le i,j \le K}\mathbb{1}\{G_1^{(i)} = G_2^{(j)}\} = 1 - \frac{1}{K^2}\langle \mathbf{g}_1, \mathbf{g}_2\rangle,$$

the probability that one copy picked at random from each draw differs; it takes values in $[0,1]$ and reduces for $K = 2$ to the diploid genotype dissimilarity $D_2$. It is not a metric: $\mathcal{D}(\mathbf{g},\mathbf{g}) > 0$ unless $\mathbf{g}$ is homozygous.

**Identity states.** Unordered pairs of draws, modulo relabelling of the objects, are called identity states; they are orbits of permutation-group actions on pairs of count vectors, can be enumerated for each $(K, I)$, and each has an explicit probability, a symmetrised sum over injective labellings $i_1,\dots,i_N$ of $\prod_j p_{i_j}^{g_1^{(j)}} q_{i_j}^{g_2^{(j)}}$ weighted by multinomial coefficients and the stabiliser size.

**Theorem.** For all $K \ge 2$, $I \ge 2$ and probability vectors $\mathbf{p}, \mathbf{q}$:
1. $\mathbb{E}[\mathcal{D}(\mathbf{p},\mathbf{q})] = 1 - \langle \mathbf{p}, \mathbf{q}\rangle$, independent of $K$.
2. $\mathbb{E}[\mathcal{D}(\mathbf{p},\mathbf{p})] \le \mathbb{E}[\mathcal{D}(\mathbf{p},\mathbf{q})]$ iff $\langle \mathbf{p}, \mathbf{q}\rangle \le \langle \mathbf{p}, \mathbf{p}\rangle$.
3. $\frac12\big(\mathbb{E}[\mathcal{D}(\mathbf{p},\mathbf{p})] + \mathbb{E}[\mathcal{D}(\mathbf{q},\mathbf{q})]\big) \le \mathbb{E}[\mathcal{D}(\mathbf{p},\mathbf{q})]$, with equality iff $\mathbf{p} = \mathbf{q}$.

Thus the mean within-population dissimilarity never exceeds the between-population one, the analogue for $K$-ploid draws of the nonnegativity of $F_{ST}$-type differentiation, and the mean between-population dissimilarity is one minus the probability that two single copies are identical in state.

## Expansion

Part 1 follows by linearity of expectation without the identity-state machinery: each of the $K^2$ pairs $(G_1^{(i)}, G_2^{(j)})$ consists of independent draws from $\mathbf{p}$ and $\mathbf{q}$, which match with probability $\langle\mathbf{p},\mathbf{q}\rangle$; the paper verifies it also by summing the identity-state probabilities. Part 3 is the inequality $\frac12(\|\mathbf{p}\|^2 + \|\mathbf{q}\|^2) \ge \langle\mathbf{p},\mathbf{q}\rangle$, i.e. $\|\mathbf{p} - \mathbf{q}\|^2 \ge 0$.

## Sources

- Zarif Ahsan, Xiran Liu and Noah A. Rosenberg, "Combinatorics of a dissimilarity measure for pairs of draws from discrete probability vectors on finite sets of objects", arXiv:2410.00221 (2024), Section 2 (definition of the dissimilarity), Theorem 3.1, Corollary 3.2, Theorem 4.1, Corollary 4.2 and Theorem 4.3, <https://doi.org/10.48550/arXiv.2410.00221>.
