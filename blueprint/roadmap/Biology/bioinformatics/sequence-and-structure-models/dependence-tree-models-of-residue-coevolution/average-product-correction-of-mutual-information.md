# Average product correction of column mutual information

Let $I_{ij}$ be the mutual information between alignment columns $i$ and $j$ ($1 \le i \ne j \le w$), and write $\langle I_{i\cdot} \rangle = \frac{1}{w - 1}\sum_{j \ne i} I_{ij}$ and $\langle I_{\cdot\cdot} \rangle = \frac{1}{w(w-1)}\sum_{i \ne j} I_{ij}$. Suppose that $I_{ij} = I^{\mathrm{true}}_{ij} + I^{b}_{ij}$ with a background contribution of product form $I^{b}_{ij} = c_i c_j$, coming from phylogenetic relatedness and entropy, and that true dependences are rare enough that their averages are negligible compared with the background averages. Then

$$I^{\mathrm{true}}_{ij} \approx I_{ij} - \frac{\langle I_{i\cdot} \rangle \langle I_{j\cdot} \rangle}{\langle I_{\cdot\cdot} \rangle},$$

the average product correction (APC). The additive variant, with background $c_i + c_j$, gives the average sum correction $I_{ij} - \langle I_{i\cdot}\rangle - \langle I_{j\cdot}\rangle + \langle I_{\cdot\cdot}\rangle$. In the dependence-tree model the same correction is applied to $\log R_{ij}$ after shifting it to be nonnegative.

## Depends on

- [Dirichlet-marginal dependence ratio of alignment columns](dirichlet-dependence-ratio-of-alignment-columns.md)

## Expansion

Under the product model and negligible true averages, $\langle I_{i\cdot} \rangle \approx c_i \bar c$ and $\langle I_{\cdot\cdot} \rangle \approx \bar c^{\,2}$ up to $O(1/w)$ terms, where $\bar c$ is the mean of the $c_j$, so $\langle I_{i\cdot}\rangle\langle I_{j\cdot}\rangle / \langle I_{\cdot\cdot}\rangle \approx c_i c_j$ is the background of the pair and subtracting it leaves the true signal. The shift before correction is needed because $\log R_{ij}$, unlike mutual information, is negative for independent columns, and posterior edge probabilities are invariant under a common shift of all $\log R_{ij}$. Adding the APC to the dependence-tree posterior gave the best contact predictions among the methods compared.

## Sources

- Burger L, van Nimwegen E. Disentangling direct from indirect co-evolution of residues in protein alignments. *PLoS Computational Biology* (2010), Materials and Methods, "Probabilistic model", "Calculating posteriors" and "Phylogenetic correction", equations (2)–(15) and (27). DOI <https://doi.org/10.1371/journal.pcbi.1000633>. PMCID PMC2793430.
