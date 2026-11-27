# Moving-average chromosomal expression profile

Let $y_{ig}$ be the normalized expression (for example $\log_2(\mathrm{TPM}+1)$) of gene $g$ in cell $i$, and let $\mu_g$ and $\sigma_g$ be the mean and standard deviation of that gene across a reference panel of normal tissue samples processed on the same scale; genes with $\sigma_g = 0$ in the reference are excluded. Define the standardized expression

$$z_{ig} = \frac{y_{ig} - \mu_g}{\sigma_g}.$$

Order the genes by chromosome and start coordinate, writing $g_1, g_2, \dots, g_G$ for that order, and fix a window size $w \ge 1$; the source uses $w = 150$ genes. With $h = \lfloor (w-1)/2 \rfloor$, the inferred chromosomal profile of cell $i$ at the gene in position $t$ is the moving average over the $w$ consecutive genes from position $t - h$ to $t - h + w - 1$,

$$s_{i,t} = \frac{1}{w} \sum_{u = t - h}^{t - h + w - 1} z_{i,g_u},$$

restricted to positions whose window lies inside one chromosome, and recentred across genes. For odd $w$ the window is centred at $t$; for even $w$, such as the published $150$, it has one more gene after $t$ than before it. A sustained positive or negative run of $s_{i,\cdot}$ over a chromosomal segment is read as a candidate gain or loss in cell $i$; agreement with exome-derived copy number is assessed by binning both into fixed-width windows (for example $10$ Mb) and correlating them.

## Remarks

A single gene's expression is far too noisy, and far too dependent on cell state, to report its own copy number; averaging over a window of neighbouring genes exploits the fact that copy-number events span many consecutive genes while regulatory variation does not, so the signal adds coherently and the noise averages down roughly as $w^{-1/2}$. The price is resolution: a window of $w$ genes cannot localize a breakpoint more precisely than the span of those genes, and focal events shorter than the window are attenuated toward zero. Standardizing against normal reference tissue, rather than against the other cells in the sample, is what keeps the baseline from being defined by the malignant cells themselves when they dominate the mixture. The method infers relative, not absolute, copy number: a uniform ploidy change shifts every window equally and is removed by the recentring step.

## Sources

- Chung W, Eum HH, Lee HO, et al. Single-cell RNA-seq enables comprehensive tumour and immune cell profiling in primary breast cancer. *Nature Communications* 8:15081 (2017), Methods, "Copy number inference from RNA-seq data". DOI <https://doi.org/10.1038/ncomms15081>. PMCID PMC5424158.
