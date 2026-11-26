# Binned logarithmic score and linear-pool ensembles

Let a forecasting target take values in one of finitely many bins $\{1, \dots, B\}$ (for example peak week, or binned peak incidence). A forecast is a probability vector $p = (p_1, \dots, p_B)$ with $p_b \ge 0$ and $\sum_b p_b = 1$. If the observed outcome falls in bin $o$, the **logarithmic score** of the forecast is $\log p_o$ (equal to $-\infty$ if $p_o = 0$), and over $n$ forecasts with observed bins $o_1, \dots, o_n$ the average score is

$$S_n = \frac{1}{n} \sum_{i=1}^{n} \log p^{(i)}_{o_i} .$$

Higher is better. The **null forecast** assigns $1/B$ to every bin and scores $-\log B$. An equal-weight **ensemble** (linear pool) of forecasts $p^{(1)}, \dots, p^{(J)}$ is $\bar p = \frac{1}{J} \sum_j p^{(j)}$.

**Proposition.**

1. *(Strict propriety.)* If the outcome is distributed according to $q$, the expected score $\sum_b q_b \log p_b$ is uniquely maximized over forecasts $p$ by $p = q$; the shortfall of any $p$ equals the Kullback–Leibler divergence $\mathrm{KL}(q \,\|\, p) \ge 0$.
2. *(Ensemble advantage.)* For every outcome $o$, $\log \bar p_o \ge \frac{1}{J} \sum_j \log p^{(j)}_o$, so the ensemble's average score is at least the mean of its members' average scores; and $\bar p_o > 0$ whenever any member gives the outcome positive probability, so the ensemble never scores $-\infty$ unless all members do.

## Proof depends on

- [Gibbs' inequality](../../../../Chemistry/chemical-thermodynamics/canonical-ensemble-of-a-finite-system/sum-mul-log-div-nonneg.md)

## Expansion

Part 1 is Gibbs' inequality: $\sum_b q_b \log q_b - \sum_b q_b \log p_b = \mathrm{KL}(q \| p)$, which is zero exactly when $p = q$. Part 2 is Jensen's inequality for the concave logarithm applied outcome by outcome and then averaged. In the open dengue forecasting challenge for San Juan and Iquitos (eight seasons, 16 teams), forecasts were scored with exactly this average log score; some forecasts assigned zero probability to the observed outcome, an ensemble formed by averaging the bin probabilities of all team forecasts and a seasonal ARIMA baseline outperformed most individual models and was the only forecast to beat the null model for every target, and calibration was strongly associated with skill.

## Sources

- M. A. Johansson, K. M. Apfeldorf, S. Dobson, et al., "An open challenge to advance probabilistic forecasting for dengue epidemics", Proceedings of the National Academy of Sciences of the USA 116 (2019), Materials and Methods ("Evaluation") and Results, <https://doi.org/10.1073/pnas.1909865116> (PMC6883829).
