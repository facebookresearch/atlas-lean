# Points-based Bayesian odds of pathogenicity

Fix a prior probability of pathogenicity $\pi_0\in(0,1)$ and a base odds factor $c>1$ (the conditional odds of pathogenicity, $\mathrm{Odds}_{\mathrm{path}}$, of one piece of *supporting* evidence). Assume the evidence items are conditionally independent given the variant's true status (naive Bayes). An item worth $x$ points (positive for pathogenic evidence, negative for benign evidence) multiplies the prior odds by $c^{x}$, so a variant with total points $S$ has

$$\mathrm{Odds}_{\mathrm{path}}=c^{S},\qquad \Pr(\text{pathogenic}\mid\text{evidence})=\frac{c^{S}\pi_0}{(c^{S}-1)\pi_0+1}.$$

The posterior is strictly increasing in $S$, and a classification threshold $p^*$ is reached exactly when

$$S\ge\log_c\frac{p^*(1-\pi_0)}{(1-p^*)\pi_0}.$$

In the framework used for clinical variant classification, $\pi_0=0.102$ and $c=2.08$. Then $+6$ points ($\mathrm{Odds}_{\mathrm{path}}\approx81.0$) gives posterior $\approx0.90$ (likely pathogenic), $+10$ points ($\approx1516$) gives posterior $\approx0.994\ge0.99$ (pathogenic), $+7$ points gives $\approx0.95$, and $+5$ points corresponds to $\mathrm{Odds}_{\mathrm{path}}\approx38.9$. The ClinGen guidance caps all locus-level evidence (phenotype specificity PP4 plus co-segregation PP1) at $+5$ points per allele, so that locus evidence alone cannot make a variant likely pathogenic.

## Expansion

Bayes' rule in odds form gives posterior odds $=$ prior odds $\times\prod_j(\text{likelihood ratio of item }j)$ under conditional independence; writing each likelihood ratio as $c^{x_j}$ turns the product into $c^{\sum_jx_j}$, and converting odds $o$ back to probability $o/(1+o)$ gives the displayed formula. Numerically, $2.08^5=38.9$, $2.08^6=81.0$, $2.08^7=168.4$ and $2.08^{10}=1516$; for example $81.0\times0.102/(80.0\times0.102+1)=0.902$. The source suggests rebasing the system on $c=2$ (the odds contributed by one informative meiosis) with prior $0.125$.

## Sources

- L. G. Biesecker, A. B. Byrne, S. M. Harrison et al., *ClinGen guidance for use of the PP1/BS4 co-segregation and PP4 phenotype specificity criteria for sequence variants*, The American Journal of Human Genetics 111 (2024), 24–38, <https://doi.org/10.1016/j.ajhg.2023.11.009> (PMCID: PMC10806742). Material and methods (prior $0.102$, $\mathrm{Odds}_{\mathrm{path}}$ of supporting evidence $2.08{:}1$), the cap on locus evidence at $+5.0$ points with the odds and posterior thresholds quoted in Results, and the Discussion on rebasing to $2.0{:}1$ with prior $0.125$; the underlying Bayesian adaptation is Tavtigian et al. (2018, 2020), cited there.
