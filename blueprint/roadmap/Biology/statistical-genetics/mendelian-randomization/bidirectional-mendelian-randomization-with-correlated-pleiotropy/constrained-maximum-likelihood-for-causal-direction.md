# Constrained maximum likelihood for causal direction

**Data.** For $m$ candidate variants, GWAS summary statistics of sample sizes $N_1$ (trait $X$) and $N_2$ (trait $Y$) give effect estimates $\hat\beta_{Xg}$ with standard errors, converted to sample correlations

$$r_{Xg} = \frac{\hat\beta_{Xg}}{\sqrt{\hat\beta_{Xg}^2 + (N_1 - 2)\,\mathrm{SE}(\hat\beta_{Xg})^2}}, \qquad \mathrm{SE}(r_{Xg}) = \frac{1 - r_{Xg}^2}{\sqrt{N_1}},$$

and likewise $r_{Yg}$; asymptotically $r_{Xg} \sim \mathcal N(\rho_{Xg},\sigma^2_{Xg})$, $r_{Yg}\sim\mathcal N(\rho_{Yg},\sigma^2_{Yg})$.

**Estimator (CD-cML).** Under the correlation-scale model $\rho_{Yg} = K_{XY}\rho_{Xg} + b_{XYg}$, maximize

$$L_{XY} = -\frac12\sum_g\Big[\frac{(r_{Xg} - \rho_{Xg})^2}{\mathrm{SE}(r_{Xg})^2} + \frac{(r_{Yg} - K_{XY}\rho_{Xg} - b_{XYg})^2}{\mathrm{SE}(r_{Yg})^2}\Big]$$

over $(K_{XY},\{\rho_{Xg}\},\{b_{XYg}\})$ subject to $\sum_g\mathbf 1[b_{XYg} \ne 0] = m_I$, for each $m_I \in \{0,\dots,m-2\}$, and choose $\hat m_I$ minimizing $\mathrm{BIC}(m_I) = -2L_{XY}(\hat\cdot\,(m_I)) + \log(n)\,m_I$ with $n = \min(N_1,N_2)$.

**Theorem.** Assume (plurality) that the true invalid set $B^0_{XY}$, $|B^0_{XY}| = m^0_{XY}$, is the only set of that size whose complement is fitted by a single slope, and that $\mathrm{SE}(r_{Xg})^2 \asymp 1/N_1$, $\mathrm{SE}(r_{Yg})^2 \asymp 1/N_2$ and $N_1 \asymp N_2$. If $m^0_{XY} \le m-2$, then as $N_1,N_2\to\infty$, $\Pr(\hat m_I = m^0_{XY}) \to 1$, the selected invalid set equals $B^0_{XY}$ with probability tending to $1$, and

$$\sqrt V\,(\hat K_{XY} - K_{XY}) \xrightarrow{d} \mathcal N(0,1), \qquad V = \sum_{g \notin B^0_{XY}}\frac{\rho_{Xg}^2}{\sigma_{Xg}^2K_{XY}^2 + \sigma_{Yg}^2},$$

with $V$ consistently estimated by $\hat V = \sum_{g\notin\hat B}\big(r_{Xg}^2 - \mathrm{SE}(r_{Xg})^2\big)/\big(\mathrm{SE}(r_{Xg})^2\hat K_{XY}^2 + \mathrm{SE}(r_{Yg})^2\big)$.

## Depends on

- [Correlation-scale model of bidirectional causation](correlation-scale-model-of-bidirectional-causation.md)

## Proof depends on

Its proof is that of the source below, as the Expansion describes.

## Expansion

For fixed invalid set the problem is an errors-in-variables regression with nuisance true correlations $\rho_{Xg}$; profiling them out gives the variance weights $\sigma^2_{Xg}K^2 + \sigma^2_{Yg}$ in $V$. The $\ell_0$ constraint lets each invalid variant absorb its own intercept, so no InSIDE-type independence between instrument strength and pleiotropy is needed, which is exactly what correlated pleiotropy breaks; BIC is selection-consistent because omitting a truly invalid variant costs a likelihood penalty of order $N$ while each extra free intercept costs only $\log n$. Running the procedure in both directions and testing $K_{XY} = 0$, $K_{YX} = 0$ (with $|\hat K| < 1$) decides between no effect, one direction and feedback; screening variants by which trait they are more strongly correlated with reduces violations of plurality by reverse-direction instruments.

## Sources

- H. Xue, W. Pan, "Robust inference of bi-directional causal relationships in presence of correlated pleiotropy with GWAS summary data", PLoS Genetics 18(5) (2022) e1010205, Methods 4.2, Eqs (13)–(17), Assumptions 1–2 and Theorem 1, <https://doi.org/10.1371/journal.pgen.1010205>, PMCID PMC9135345.
