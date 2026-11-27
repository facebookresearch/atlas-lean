# Negative-binomial mixture model with expression-dependent dropout

**Model (BUSseq).** Cells $i = 1,\dots,n_b$ in batches $b = 1,\dots,B$ are measured on genes $g = 1,\dots,G$. With cell-type indicator $W_{bi}$, true count $X_{big}$, dropout indicator $Z_{big}$ and observed count $Y_{big}$:

$$\Pr(W_{bi} = k) = \pi_{bk}, \qquad X_{big}\mid W_{bi} = k \sim \mathrm{NB}(\mu_{big},\phi_{bg}), \qquad \log\mu_{big} = \alpha_g + \beta_{gk} + \nu_{bg} + \delta_{bi},$$

$$Z_{big}\mid X_{big} = x \sim \mathrm{Bernoulli}(p_{big}), \quad \log\frac{p_{big}}{1-p_{big}} = \gamma_{b0} + \gamma_{b1}x, \qquad Y_{big} = X_{big}(1 - Z_{big}),$$

with baseline expression $\alpha_g$, cell-type effects $\beta_{gk}$ ($\beta_{g1} = 0$), location batch effects $\nu_{bg}$ ($\nu_{1g} = 0$), size factors $\delta_{bi}$ ($\delta_{b1} = 0$), overdispersions $\phi_{bg}$, and $f_{\mathrm{NB}}(x;\mu,\phi) = \binom{\phi+x-1}{x}\big(\tfrac{\mu}{\mu+\phi}\big)^x\big(\tfrac{\phi}{\mu+\phi}\big)^\phi$.

**Observed-data likelihood.**

$$L_o(\Theta \mid y) = \prod_{b=1}^B\prod_{i=1}^{n_b}\Big[\sum_{k=1}^K \pi_{bk}\prod_{g=1}^G \Pr(Y_{big} = y_{big} \mid W_{bi} = k, \Theta)\Big],$$

where, writing $\mu = e^{\alpha_g+\beta_{gk}+\nu_{bg}+\delta_{bi}}$ and $\sigma(t) = e^t/(1+e^t)$,

$$\Pr(Y_{big} = 0 \mid k) = f_{\mathrm{NB}}(0;\mu,\phi_{bg}) + \sum_{x \ge 1}\sigma(\gamma_{b0} + \gamma_{b1}x)\,f_{\mathrm{NB}}(x;\mu,\phi_{bg}),$$

$$\Pr(Y_{big} = y \mid k) = \big(1 - \sigma(\gamma_{b0}+\gamma_{b1}y)\big)\,f_{\mathrm{NB}}(y;\mu,\phi_{bg}), \quad y > 0.$$

## Depends on

- [Negative binomial mass function with size and mean](../../../../Probability/distributions/discrete/negative-binomial-and-beta-binomial-distribution/negative-binomial/neg-binomial-real.md)

## Expansion

An observed zero is either a biological zero ($X = 0$) or a dropout of a positive count, and the dropout probability depends on the unobserved count itself, so the missingness is not at random; the sum over $x$ integrates the latent count out. Because batch effects $\nu_{bg}$ are additive on the log-mean scale while cell-type effects $\beta_{gk}$ are shared across batches, differences between two cell types are the same in every batch, which is the lever that makes batch effects estimable. Posterior sampling of $W$, $X$ and $Z$ yields cell-type clusters, batch-corrected counts and imputed dropouts.

## Sources

- F. Song, G. M. A. Chan, Y. Wei, "Flexible experimental designs for valid single-cell RNA-sequencing experiments allowing batch effects correction", Nature Communications 11 (2020) 3274, Methods (BUSseq model), Eq (1), <https://doi.org/10.1038/s41467-020-16905-2>, PMCID PMC7330047.
