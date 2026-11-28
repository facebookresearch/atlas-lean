# Reference-panel LD error in summary-statistic fine-mapping

Consider two variants, one causal ($C$) and one non-causal ($N$), with population correlation $\rho$, standardized genotypes, small causal effect $\lambda_C$ and a GWAS of size $n$, so that the $z$-scores satisfy $\hat{\mathbf z} \approx \sqrt n\, R \boldsymbol\lambda$. Fine-mapping uses the FINEMAP-type Bayes factors with prior effect variance $s_\lambda^2$, equal prior probabilities $1/3$ on the configurations "only $C$ causal" ($\gamma_{10}$), "only $N$ causal" ($\gamma_{01}$) and "both causal" ($\gamma_{11}$), and an LD correlation $\tilde\rho = \rho + \varepsilon/\sqrt d$ estimated from a reference panel of $d$ individuals, where $\varepsilon \sim N(0, 1 - \rho^2)$.

**Exact posterior odds.**

$$\frac{\Pr(\gamma_{10} \mid D)}{\Pr(\gamma_{11} \mid D)} = \frac{N(\hat z_C \mid 0, 1 + n s_\lambda^2)\,/\,N(\hat z_C \mid 0, 1)}{N(\hat{\mathbf z} \mid \mathbf 0, \tilde R + n s_\lambda^2 \tilde R \tilde R)\,/\,N(\hat{\mathbf z} \mid \mathbf 0, \tilde R)},$$

with $\tilde R$ the $2 \times 2$ correlation matrix built from $\tilde\rho$.

**Asymptotics.** For large $n$ and $d$, dropping terms bounded independently of $n$ and $d$,

$$2\log \frac{\Pr(\gamma_{10} \mid D)}{\Pr(\gamma_{11} \mid D)} \approx \log n - \frac{n}{d}\, \frac{\lambda_C^2\, \varepsilon^2}{1 - \rho^2}, \qquad \mathbb E\Bigl[2\log \frac{\Pr(\gamma_{10} \mid D)}{\Pr(\gamma_{11} \mid D)}\Bigr] \approx \log n - \frac{n}{d}\lambda_C^2 .$$

The factor $2$ on the left corrects the source. Benner et al. print Equations A4–A5 as "log{Pr(γ10|D)/Pr(γ11|D)} ≈ log n − …", without it, but their Equation A1 writes the log odds with a factor $0.5$ on every term and Equations A2–A3 accordingly read "2 log{Pr(γ10|D)/Pr(γ11|D)} = log n + …". Read without the $2$, A4–A5 differ from A1–A3 by an amount unbounded in $n$ (at $\varepsilon = 0$ they give $\log n$ instead of $\tfrac12\log n$); the sign conclusions below are the same for both forms.

Hence if $n \gg d$ the false configuration with two causal variants is on average favoured, while if $d$ grows proportionally to $n$ the evidence for the true configuration grows like $\log n$. The reference panel must scale with the GWAS sample size.

## Expansion

With in-sample LD ($\varepsilon = 0$) the log odds grow like $\log n$, the Occam penalty against the superfluous second effect. With reference LD the quadratic form $\hat{\mathbf z}^\top (I/(n s_\lambda^2) + \tilde R)^{-1}\hat{\mathbf z}$ acquires a residual $n\lambda_C^2\varepsilon^2/d$ that is linear in $n$. The model explains the mismatch between observed $z$-scores and the panel LD by adding a causal effect at $N$, so the linear term eventually dominates $\log n$. Empirically, a panel of $1{,}000$ individuals from the target population was adequate for GWAS of up to about $10{,}000$ individuals, while 1000 Genomes-sized panels were not.

## Sources

- C. Benner, A. S. Havulinna, M.-R. Järvelin, et al., "Prospects of Fine-Mapping Trait-Associated Genomic Regions by Using Summary Statistics from Genome-wide Association Studies", *American Journal of Human Genetics* (2017), <https://doi.org/10.1016/j.ajhg.2017.08.012> (PMC5630179; Appendix A, Equations A1–A5).
