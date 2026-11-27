# Terminal, simultaneous and subsequent association scores on a phylogeny

**Setting.** Let a rooted phylogeny of $n$ sampled genomes have $n_b$ branches. For a biallelic locus, let $g \in [0,1]$ be the genotype state (presence of the allele, or its posterior probability from ancestral reconstruction) and for the phenotype let $p \in [0,1]$ (binary, or a continuous phenotype rescaled to $[0,1]$). For branch $i$ write $g_i^{\mathrm{anc}}, p_i^{\mathrm{anc}}$ for the reconstructed states at its upper (ancestral) node and $g_i^{\mathrm{des}}, p_i^{\mathrm{des}}$ for its lower (descendant) node; at leaves, the descendant states are the observed data.

**Definitions.**

$$\text{Score}_1 = \left|\frac1n \sum_{i=1}^{n} \Big[p_i^{\mathrm{des}} g_i^{\mathrm{des}} + (1 - p_i^{\mathrm{des}})(1 - g_i^{\mathrm{des}}) - (1 - p_i^{\mathrm{des}}) g_i^{\mathrm{des}} - p_i^{\mathrm{des}}(1 - g_i^{\mathrm{des}})\Big]\right| \quad (\text{sum over leaves}),$$

$$\text{Score}_2 = \left|\sum_{i=1}^{n_b} \big(p_i^{\mathrm{anc}} - p_i^{\mathrm{des}}\big)\big(g_i^{\mathrm{anc}} - g_i^{\mathrm{des}}\big)\right|,$$

$$\text{Score}_3 = \left|\sum_{i=1}^{n_b} \Big[\tfrac43 p_i^{\mathrm{anc}} g_i^{\mathrm{anc}} + \tfrac23 p_i^{\mathrm{anc}} g_i^{\mathrm{des}} + \tfrac23 p_i^{\mathrm{des}} g_i^{\mathrm{anc}} + \tfrac43 p_i^{\mathrm{des}} g_i^{\mathrm{des}} - p_i^{\mathrm{anc}} - p_i^{\mathrm{des}} - g_i^{\mathrm{anc}} - g_i^{\mathrm{des}} + 1\Big]\right| .$$

**Properties.**

1. *Terminal score.* The bracket in $\text{Score}_1$ equals $(2p - 1)(2g - 1)$, so $\text{Score}_1 = \big|\frac1n\sum_{\text{leaves}} (2p_i - 1)(2g_i - 1)\big|$; for binary data it is $|n_{11} + n_{00} - n_{10} - n_{01}|/n$ in terms of the four leaf state combinations. It ignores ancestral reconstruction and is robust to errors in the tree.
2. *Simultaneous score.* For binary states on a parsimonious reconstruction, each branch contributes $\pm 1$ exactly when both genotype and phenotype change on it ($+1$ if they change in the same direction), so $\text{Score}_2$ counts parallel substitutions; branches where at most one variable changes contribute zero, so the score accumulates evidence from repeated co-occurring changes without requiring sample-wide association.
3. *Subsequent score.* If $p$ and $g$ are interpolated linearly along branch $i$, $P(s) = p^{\mathrm{anc}} + s(p^{\mathrm{des}} - p^{\mathrm{anc}})$, $G(s)$ likewise, $s \in [0,1]$, then the branch term equals

$$\int_0^1 \big(2P(s) - 1\big)\big(2G(s) - 1\big)\, ds,$$

so $\text{Score}_3$ integrates the leaf-style association over the whole tree; it rewards association maintained across branches even when the genotype and phenotype changed on different, successive branches.

## Expansion

Property 1 is the expansion $(2p-1)(2g-1) = 4pg - 2p - 2g + 1 = pg + (1-p)(1-g) - (1-p)g - p(1-g)$. For property 3, $\int_0^1 P G\, ds = \tfrac13 p^{a}g^{a} + \tfrac16 p^{a}g^{d} + \tfrac16 p^{d}g^{a} + \tfrac13 p^{d}g^{d}$ and $\int_0^1 2P\,ds = p^{a} + p^{d}$; substituting into $4PG - 2P - 2G + 1$ gives the summand of $\text{Score}_3$. The three scores capture complementary patterns (widespread terminal association, convergent co-occurring changes, and association that arises on one branch and persists downstream), and each is tested separately against a phylogenetically matched null distribution; the union of significant loci is reported, with a multiple-testing correction across loci and the three tests.

## Sources

- Collins C, Didelot X, "A phylogenetic method to perform genome-wide association studies in microbes that accounts for population structure and recombination" (2018), Methods, Equations (1)–(3) and Figure 1 (treeWAS association scores; the integral form of Score 3 is derived in S3 Appendix), <https://doi.org/10.1371/journal.pcbi.1005958>, PMCID PMC5814097.
