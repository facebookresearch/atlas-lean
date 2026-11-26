# Rao–Blackwellized exposure effect under randomized instrument selection

**Setting.** For independent SNPs $j=1,\dots,p$, the exposure GWAS reports $\hat\beta_{Xj}\sim N(\beta_{Xj},\sigma_{Xj}^2)$ with known $\sigma_{Xj}$. Selecting SNPs by $|\hat\beta_{Xj}/\sigma_{Xj}|>\lambda$ and reusing $\hat\beta_{Xj}$ overestimates $|\beta_{Xj}|$ (winner's curse): conditional on selection, $\hat\beta_{Xj}$ follows a truncated Gaussian law whose mean is not $\beta_{Xj}$.

**Randomized selection.** Draw independent pseudo-noise $Z_j\sim N(0,\eta^2)$ and select

$$\mathcal S_\lambda=\Bigl\{j:\ \Bigl|\frac{\hat\beta_{Xj}}{\sigma_{Xj}}+Z_j\Bigr|>\lambda\Bigr\},\qquad s_\lambda=|\mathcal S_\lambda| .$$

**Rao–Blackwellized estimate.** With $\phi,\Phi$ the standard normal density and distribution function and

$$A_{j,\pm}=-\frac{\hat\beta_{Xj}}{\sigma_{Xj}\eta}\pm\frac{\lambda}{\eta},$$

the estimator

$$\hat\beta_{Xj,RB}=\hat\beta_{Xj}-\frac{\sigma_{Xj}}{\eta}\cdot\frac{\phi(A_{j,+})-\phi(A_{j,-})}{1-\Phi(A_{j,+})+\Phi(A_{j,-})},\qquad j\in\mathcal S_\lambda,$$

is unbiased for $\beta_{Xj}$ conditional on selection. Its plug-in variance is

$$\hat\sigma^2_{Xj,RB}=\sigma_{Xj}^2\left[1-\frac{1}{\eta^2}\cdot\frac{A_{j,+}\phi(A_{j,+})-A_{j,-}\phi(A_{j,-})}{1-\Phi(A_{j,+})+\Phi(A_{j,-})}+\frac{1}{\eta^2}\left(\frac{\phi(A_{j,+})-\phi(A_{j,-})}{1-\Phi(A_{j,+})+\Phi(A_{j,-})}\right)^2\right].$$

The denominator $1-\Phi(A_{j,+})+\Phi(A_{j,-})$ is the selection probability $P(j\in\mathcal S_\lambda\mid\hat\beta_{Xj})$. The recommended default is $\eta=0.5$.

## Expansion

The randomized event depends on the data only through $\hat\beta_{Xj}+\sigma_{Xj}Z_j$. Conditioning on selection, $\hat\beta_{Xj}-\sigma_{Xj}Z_j/\eta^2$ (suitably scaled) is independent of the selection statistic, so it stays unbiased; Rao–Blackwellizing it, i.e. taking its conditional expectation given $\hat\beta_{Xj}$ and the selection event, removes the added noise and gives the closed form above as a truncated-normal mean correction. The correction is negligible for strong instruments far from the cutoff, which are selected with probability close to one, and acts mainly on SNPs near $\lambda$.

## Sources

- Z. Xie, W. Zhang, J. Wang, C. Wu, "Winner's Curse Free Robust Mendelian Randomization with Summary Data", *Journal of the American Statistical Association* (2026), Section 2 (winner's curse bias) and Section 3.2 (randomized instrument selection and the Rao–Blackwellized estimator and its variance), building on Ma, Wang and Wu (2023), <https://doi.org/10.1080/01621459.2025.2587321>, PMCID PMC13004071.
