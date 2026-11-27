# MR-SPLIT cross-fitted exposures for one-sample Mendelian randomization

In a one-sample Mendelian randomization study with $N$ individuals, outcome $Y$, exposure $X$ and many candidate SNP instruments $G = (G_1, \dots, G_J)$, the two-stage least squares (2SLS) estimate of the causal effect $\beta$ in $Y = \beta X + u$ is biased when the same data both select instruments and estimate effects (winner's curse, or selection bias) and when many instruments are weak (bias toward the confounded OLS estimate).

**MR-SPLIT.** Randomly split the sample into halves $I_1, I_2$. For $k \in \{1,2\}$:

1. In $I_k$, select instruments and estimate their exposure effects $\hat\alpha_{k,j}$; split the selected set into **major** instruments $S_{k,M}$ and **weak** instruments $S_{k,W}$ by a partial $F$-statistic threshold, $F = \frac{(\mathrm{RSS}_r - \mathrm{RSS}_f)/(p-k)}{\mathrm{RSS}_f/(N-p)}$, comparing models with and without each instrument.
2. In the complementary half $I_{k}^c$, combine the weak instruments into one composite instrument

$$\hat G_{k^c, W} = \sum_{j \in S_{k,W}} \omega_j\, G_{k^c, j}, \qquad \omega_j = \frac{\operatorname{sign}(\hat\alpha_{k,j})\,|\hat\alpha_{k,j}|}{\sum_{j' \in S_{k,W}} |\hat\alpha_{k,j'}|},$$

and regress $X$ on $\{G_{k^c, M}, \hat G_{k^c,W}\}$ in $I_k^c$ to obtain cross-fitted exposures $\hat X_{k^c}$.

Stack $\hat X = (\hat X_1^\top, \hat X_2^\top)^\top \in \mathbb{R}^N$ and estimate on the whole sample

$$\hat\beta = (\hat X^\top \hat X)^{-1} \hat X^\top Y .$$

Repeating over $L$ random splits improves robustness to a particular split: the estimate is the average $\hat\beta = \frac1L\sum_{l=1}^L \hat\beta_l$ of the per-split estimates, and the per-split p-values are combined by the Cauchy combination rule, $T = \frac1L\sum_{l=1}^L \tan\big((\tfrac12 - p_l)\pi\big)$ and $p = \tfrac12 - \arctan(T)/\pi$.

**Theorem.** With a 2-fold random split, the MR-SPLIT estimator is at least as efficient as the cross-fitting estimator that combines cross-fitted composite instruments (CFMR):

$$\operatorname{var}(\hat\beta_{\mathrm{MR\text{-}SPLIT}}) \le \operatorname{var}(\hat\beta_{\mathrm{CFMR}}).$$

## Depends on

- [Linear moment model for instrumental variables](linear-moment-model.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

Because instruments and their weights are chosen in one half and applied in the other, the fitted exposure in each half is independent of that half's outcome noise, removing the selection (winner's curse) bias while still using all $N$ observations in the second stage. Collapsing the weak instruments into a single weighted score keeps their information but reduces the number of instruments, which limits weak-instrument bias of 2SLS. Combining cross-fitted exposures rather than cross-fitted instruments is what yields the variance comparison; simulations indicate the same ordering for more than two folds.

## Sources

- R. Shi, L. Wang, S. Burgess and Y. Cui, "MR-SPLIT: a novel method to address selection and weak instrument bias in one-sample Mendelian randomization studies", PLoS Genetics 20 (2024), Methods, Eqs. (1)–(4), Remarks 1–3 and Theorem 1, <https://doi.org/10.1371/journal.pgen.1011391>, PMCID: PMC11410202.
