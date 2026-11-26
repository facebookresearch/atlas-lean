# Correlation-scale model of bidirectional causation

**Model.** Traits $X, Y$, an unmeasured confounder $U$, and three groups of variants — $g_X$ acting only on $X$, $g_Y$ only on $Y$, and $g_B$ on both (directly or through $U$) — satisfy the linear structural equations

$$U = \xi g_B + \epsilon_U,\qquad X = \theta_{YX}Y + \alpha g_X + \gamma g_B + \theta_{UX}U + \epsilon_X,\qquad Y = \theta_{XY}X + \beta g_Y + \eta g_B + \theta_{UY}U + \epsilon_Y,$$

with independent errors and $\theta_{XY}\theta_{YX} \ne 1$. Let $\rho_{Xg}, \rho_{Yg}$ be the population correlations of a variant $g$ with $X$ and $Y$, and define

$$K_{XY} = \theta_{XY}\frac{\sqrt{\operatorname{var}X}}{\sqrt{\operatorname{var}Y}}, \qquad K_{YX} = \theta_{YX}\frac{\sqrt{\operatorname{var}Y}}{\sqrt{\operatorname{var}X}}.$$

**Proposition.**
1. For $g \in g_X$: $\rho_{Yg} = K_{XY}\,\rho_{Xg}$. For $g \in g_Y$: $\rho_{Xg} = K_{YX}\,\rho_{Yg}$. For $g \in g_B$:

$$\rho_{Yg} = K_{XY}\rho_{Xg} + b_{XYg},\quad b_{XYg} = \frac{(\eta + \theta_{UY}\xi)\operatorname{var}(g)}{\sqrt{\operatorname{var}(Y)\operatorname{var}(g)}}, \qquad \rho_{Xg} = K_{YX}\rho_{Yg} + b_{YXg},\quad b_{YXg} = \frac{(\gamma+\theta_{UX}\xi)\operatorname{var}(g)}{\sqrt{\operatorname{var}(X)\operatorname{var}(g)}}.$$

Hence for all variants $\rho_{Yg} = K_{XY}\rho_{Xg} + b_{XYg}$, with $b_{XYg} = 0$ exactly for the valid instruments $g \in g_X$ (for $g\in g_Y$, $b_{XYg} = (1/K_{YX} - K_{XY})\rho_{Xg}$).
2. $K_{XY} \ne 0 \iff \theta_{XY} \ne 0$, and $|K_{XY}| < 1$ whenever $\theta_{XY}^2\operatorname{var}(X) < \operatorname{var}(Y)$ (symmetrically for $K_{YX}$).
3. Correlated pleiotropy violates the InSIDE assumption: $\xi \ne 0$ correlates $\rho_{Xg}$ with $b_{XYg}$, and even with $\xi = 0$ a reverse effect $\theta_{YX} \ne 0$ does so through $\eta$. Variants in $g_Y$ used for the direction $X\to Y$ point to the slope $1/K_{YX}$, with $|1/K_{YX}| > 1$.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

For $g \in g_X$, $\operatorname{cov}(Y,g) = \theta_{XY}\operatorname{cov}(X,g)$ because $g$ reaches $Y$ only through $X$, and dividing by the standard deviations gives the slope $K_{XY}$. Variants in $g_B$ reach $Y$ also directly or through $U$, which adds an intercept proportional to $\eta + \theta_{UY}\xi$. Standardization is what bounds the slopes: a causal slope of absolute value at least $1$ on the correlation scale would require $X$ to explain at least all of $Y$'s variance, so $|K| < 1$ distinguishes the true direction from the spurious reciprocal slope $1/K_{YX}$ produced by reverse-direction instruments. Causal direction is then read off from which of $K_{XY}, K_{YX}$ are non-zero with absolute value below $1$.

## Sources

- H. Xue, W. Pan, "Robust inference of bi-directional causal relationships in presence of correlated pleiotropy with GWAS summary data", PLoS Genetics 18(5) (2022) e1010205, Methods 4.1, Eqs (4)–(12), <https://doi.org/10.1371/journal.pgen.1010205>, PMCID PMC9135345.
