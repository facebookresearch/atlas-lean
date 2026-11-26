# LOD score for a marker effect in a multi-locus model

Let $L_1$ be the maximized natural-log likelihood of a multi-locus model containing the $q$ markers with nonzero estimated effects, and $L_0$ the maximized log likelihood of the same model with the effect of marker $k$ removed ($H_0 : \gamma_{(k)} = 0$). The LOD score of marker $k$ is the base-10 log likelihood ratio

$$\mathrm{LOD} = \log_{10}\frac{e^{L_1}}{e^{L_0}} = \frac{L_1 - L_0}{\ln 10} = \frac{-2 (L_0 - L_1)}{4.6052}.$$

Under $H_0$ and the usual regularity conditions, $2 \ln(10) \cdot \mathrm{LOD} = 4.6052 \cdot \mathrm{LOD}$ is asymptotically $\chi^2_1$, so the threshold $\mathrm{LOD} \ge 3$ corresponds to the nominal $p$-value

$$\Pr\{\chi^2_1 > 3 \times 4.6052\} = \Pr\{\chi^2_1 > 13.8155\} \approx 2.0 \times 10^{-4}.$$

## Depends on

- [EM algorithm for the multi-locus Bayesian LASSO mixed model](em-algorithm-for-the-bayesian-lasso-mixed-model.md)

## Expansion

The identity $4.6052 = 2 \ln 10$ converts the likelihood-ratio statistic $2(L_1 - L_0)$ to a decimal log odds, which is why LOD $3$ means the data are $1000$ times more probable under the model with the effect than without it. The $\chi^2_1$ calibration treats each marker test as a one-parameter nested comparison; it ignores the selection that produced the candidate set, so the stated $p$-value is nominal, which is one reason the method uses the fairly stringent LOD $3$ rather than a per-test $0.05$. In simulation the same LOD rule was applied to SCAD and to multi-locus random-SNP-effect mixed models, whereas single-locus methods used a Bonferroni threshold $0.05/m$ over $m$ markers.

## Sources

- Tamba CL, Ni YL, Zhang YM. Iterative sure independence screening EM-Bayesian LASSO algorithm for multi-locus genome-wide association studies. *PLoS Computational Biology* (2017), Methods, "Significance testing", equation (11). DOI <https://doi.org/10.1371/journal.pcbi.1005357>. PMCID PMC5308866.
