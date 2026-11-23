# Cox partial likelihood

For $n$ subjects with observed times $T_i \in \mathbb{R}$, event indicators $\delta_i \in \{0, 1\}$ ($\delta_i = 1$ for an observed event, $0$ for censoring) and covariates $x_i \in \mathbb{R}^p$, Cox's partial likelihood at $\beta \in \mathbb{R}^p$ is

$$L(\beta) = \prod_{i : \delta_i = 1} \frac{\exp\langle \beta, x_i \rangle}{\sum_{l \in R(T_i)} \exp\langle \beta, x_l \rangle},$$

with $R(T_i)$ the [risk set](risk-set.md). Tied event times are handled by Breslow's convention: each event uses its own full risk set.

## Sources

- David R. Cox, *Regression models and life-tables*, J. Roy. Statist. Soc. Ser. B 34 (1972), no. 2, 187–202, DOI 10.1111/j.2517-6161.1972.tb00899.x.
