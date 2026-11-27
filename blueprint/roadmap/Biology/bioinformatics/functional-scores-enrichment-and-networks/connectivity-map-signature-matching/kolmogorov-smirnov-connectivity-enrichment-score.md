# Kolmogorov–Smirnov connectivity enrichment score

**Setting.** A drug profile ranks $r$ genes, $1$ (most up-regulated) to $r$. A query signature is a set of $s$ genes from this ranking; sort them by their rank in the drug profile and let $V(j)$, $1 \le V(1) < \dots < V(s) \le r$, be the rank of the $j$-th signature gene.

**Definition.**

$$a = \max_{1 \le j \le s}\left( \frac{j}{s} - \frac{V(j)}{r} \right), \qquad b = \max_{1 \le j \le s}\left( \frac{V(j)}{r} - \frac{j - 1}{s} \right),$$

and the enrichment score is $\mathrm{ES} = a$ if $a > b$, and $\mathrm{ES} = -b$ otherwise. It is computed separately for the up- and down-regulated parts of a disease signature, giving $\mathrm{ES}_{\mathrm{up}}$ and $\mathrm{ES}_{\mathrm{down}}$; significance is assessed by recomputing ES for random signatures of the same sizes.

**Proposition.** $a \in [0, 1)$, $b \in (0, 1]$ and $a + b \ge 1/s$. If the signature occupies the top $s$ ranks then $a = 1 - s/r$; if it occupies the bottom $s$ ranks then $b = 1 - (s-1)/r$.

## Remarks

$a$ and $b$ are the one-sided Kolmogorov–Smirnov distances between the empirical distribution of the signature ranks, scaled to $[0,1]$, and the uniform distribution: $a$ detects concentration near the top of the profile and $b$ near the bottom. Adding the terms at the same $j$ gives $a + b \ge 1/s$. Taking $j = s$ in $a$ and $V(s) \le r$ gives $a \ge 0$, and $b \ge V(1)/r > 0$. In the original Connectivity Map the up and down scores are combined into the connectivity score $\mathrm{ES}_{\mathrm{up}} - \mathrm{ES}_{\mathrm{down}}$ when they have opposite signs and $0$ otherwise. The source counts, for each drug, how many of three coronavirus-infection signatures give $\mathrm{ES} > 0$ with permutation $p < 0.05$.

## Sources

- Y. Zhou, Y. Hou, J. Shen, Y. Huang, W. Martin and F. Cheng, *Network-based drug repurposing for novel coronavirus 2019-nCoV/SARS-CoV-2*, Cell Discov. 6 (2020), 14. <https://doi.org/10.1038/s41421-020-0153-3> (PMCID: PMC7073332). Methods, "Gene set enrichment analysis", Eq. (4).
- J. Lamb et al., *The Connectivity Map: using gene-expression signatures to connect small molecules, genes, and disease*, Science 313 (2006), 1929–1935. <https://doi.org/10.1126/science.1132939>
