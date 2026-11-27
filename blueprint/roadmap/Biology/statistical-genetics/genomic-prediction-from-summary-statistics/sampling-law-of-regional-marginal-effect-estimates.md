# Sampling law of marginal effect estimates in a linkage-disequilibrium region

Let $X^{(l)}$ be the $M_l \times N$ matrix of standardized genotypes of the markers in a region $l$ for $N$ unrelated training individuals, let $D^{(l)} = X^{(l)} X^{(l)\prime}/N$ be the regional LD (correlation) matrix, and suppose the standardized phenotype is $Y = X^{(l)\prime}\beta^{(l)} + \varepsilon$ where $\varepsilon$ collects the contributions of all other regions and noise, with $\mathbb E(\varepsilon \mid \beta^{(l)}) = 0$ and $\operatorname{Var}(\varepsilon \mid \beta^{(l)}) = (1 - h_l^2) I_N$, $h_l^2$ being the heritability explained by region $l$. Treat $X^{(l)}$ as fixed. Then the marginal least-squares estimates $\tilde\beta^{(l)} = X^{(l)} Y / N$ satisfy

$$\mathbb E\big(\tilde\beta^{(l)} \mid \beta^{(l)}\big) = D^{(l)} \beta^{(l)}, \qquad \operatorname{Var}\big(\tilde\beta^{(l)} \mid \beta^{(l)}\big) = \frac{1 - h_l^2}{N}\, D^{(l)} .$$

If $D^{(l)}$ is invertible, the joint least-squares estimate $\hat\beta^{(l)}_{\text{joint}} = (D^{(l)})^{-1}\tilde\beta^{(l)}$ is conditionally unbiased with

$$\operatorname{Var}\big(\hat\beta^{(l)}_{\text{joint}} \mid \beta^{(l)}\big) = \frac{1 - h_l^2}{N}\, (D^{(l)})^{-1}.$$

When $h_l^2$ is small this gives the approximation $\tilde\beta^{(l)} \mid \beta^{(l)} \approx \mathcal N\big(D^{(l)}\beta^{(l)}, D^{(l)}/N\big)$ used by LDpred, which allows effect estimates to be simulated from an LD matrix without simulating genotypes.

## Depends on

- [Effect-estimate model for polygenic score accuracy](prsmodel.md)
- [The LDpred-inf posterior](../../quantitative-genetics/linear-mixed-models-and-blup/cond-distrib-ldpred-inf.md)

## Expansion

$\tilde\beta^{(l)} = X^{(l)}X^{(l)\prime}\beta^{(l)}/N + X^{(l)}\varepsilon/N = D^{(l)}\beta^{(l)} + X^{(l)}\varepsilon/N$; the second term has mean zero and covariance $X^{(l)}(1-h_l^2)I_N X^{(l)\prime}/N^2 = (1-h_l^2)D^{(l)}/N$. Multiplying by $(D^{(l)})^{-1}$ gives the joint estimate's moments. Combined with a Gaussian prior on $\beta^{(l)}$, this likelihood yields the LDpred-inf posterior; combined with a point-normal prior it is the target of LDpred's approximate Gibbs sampler (Appendix A, Equation A2).

## Sources

- B. J. Vilhjálmsson, J. Yang, H. K. Finucane, et al., "Modeling Linkage Disequilibrium Increases Accuracy of Polygenic Risk Scores", American Journal of Human Genetics 97 (2015), 576–592, <https://doi.org/10.1016/j.ajhg.2015.09.001> (PMC4596916). Appendix A.
