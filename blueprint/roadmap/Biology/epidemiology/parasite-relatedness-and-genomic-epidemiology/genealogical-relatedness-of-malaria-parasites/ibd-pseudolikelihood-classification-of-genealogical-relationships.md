# IBD pseudolikelihood classification of parasite genealogical relationships

For a pair of haploid parasites with a genome of $C$ chromosomes, summarize identity by descent by three kinds of features: the genome-wide IBD fraction $r_{\mathrm{total}} \in [0,1]$; for each chromosome $i$ the length of its longest IBD segment as a fraction of the chromosome, $\mathrm{IBD}_{\max,i} \in [0, 1]$; and the number of IBD segments $n_{\mathrm{seg},i} \in \{0, 1, 2, \dots\}$. For each candidate genealogical relationship $G$ (parent–child, full siblings, meiotic siblings, half siblings, avuncular, cousins, unrelated, ...), the **pseudolikelihood** is

$$\mathcal{L}(G \mid r_{\mathrm{total}}, \mathrm{IBD}_{\max}, n_{\mathrm{seg}}) = \mathcal{L}(G \mid r_{\mathrm{total}}) \prod_{i=1}^{C} \mathcal{L}(G \mid \mathrm{IBD}_{\max,i})\, \mathcal{L}(G \mid n_{\mathrm{seg},i}),$$

with components fitted to simulations of the genealogy under a meiosis model:

- $\mathcal{L}(G \mid r_{\mathrm{total}})$ is a Beta density $\dfrac{\Gamma(\alpha_G + \beta_G)}{\Gamma(\alpha_G)\Gamma(\beta_G)} x^{\alpha_G - 1}(1 - x)^{\beta_G - 1}$;
- $\mathcal{L}(G \mid \mathrm{IBD}_{\max,i})$ is a spiked density with point masses $P_{G,i}(0)$ at $0$ (no IBD on the chromosome) and $P_{G,i}(1)$ at $1$ (the whole chromosome IBD) and a kernel density estimate on $(0, 1)$;
- $\mathcal{L}(G \mid n_{\mathrm{seg},i}) = \theta_x = \dfrac{c_x + \alpha}{N + \alpha d}$ is an additively smoothed frequency, where $c_x$ of $N$ simulations had $x$ segments, $d$ is the number of categories (including one for unseen counts) and $\alpha = 1$.

The relationship is classified by maximum pseudolikelihood, and sets of hypotheses are compared by the generalized likelihood ratio $\lambda = \max_{\theta \in \Theta_0} \mathcal{L}(\theta) / \max_{\theta \in \Theta_1} \mathcal{L}(\theta)$.

## Remarks

The product over chromosomes treats chromosomes as independent, which is justified by independent assortment and independent crossover processes on different chromosomes; within a chromosome the longest segment and the segment count capture the segment-length distribution that distinguishes relationships with equal mean relatedness. For example, parent–child pairs have fewer but longer IBD segments than full siblings, often spanning whole short chromosomes. Using $r_{\mathrm{total}}$ alone separates first-, second- and third-degree relatives but not relationships within a degree; adding the per-chromosome segment features raises the simulated true classification rate to $0.989$, $0.925$ and $0.944$ for first-, second- and third-degree relatives (relationship set without meiotic siblings). The point masses at $0$ and $1$ are needed because short chromosomes are frequently either entirely non-IBD or entirely IBD. Pseudolikelihood here means a product of separately fitted marginal models, not a joint likelihood of the IBD segments.

## Depends on

- [Expected IBD relatedness of haploid parasite genealogies](expected-ibd-relatedness-of-haploid-parasite-genealogies.md)

## Sources

- W. Wong, L. Wang, S. F. Schaffner, X. Li, I. Cheeseman, T. J. C. Anderson, A. Vaughan, M. Ferdig, S. K. Volkman, D. L. Hartl and D. F. Wirth, "MalKinID: A classification model for identifying malaria parasite genealogical relationships using identity-by-descent", *Genetics* 229 (2025), iyae197, Methods Eqs. (1)–(5) and Results, <https://doi.org/10.1093/genetics/iyae197> (PMC11796457).
