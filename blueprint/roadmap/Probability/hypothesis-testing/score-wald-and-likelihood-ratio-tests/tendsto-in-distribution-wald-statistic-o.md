# Wald's test with an estimated information

Under the regularity conditions (R) of [Wald's test](tendsto-in-distribution-wald-statistic.md), let $\hat I_n : \Omega \to \mathbb{R}$ be almost everywhere measurable estimators with $\hat I_n \to I(\theta_0)$ in probability. Then

$$n (\hat\theta_n - \theta_0)^2 \hat I_n \to \chi^2_1 \quad \text{in distribution}.$$

Examples of such estimators are the [observed information](tendsto-in-measure-observed-information.md), and $I(\hat\theta_n)$ when $\theta \mapsto I(\theta)$ is continuous at $\theta_0$ (by the continuous mapping theorem).
