# Rao's score test with an estimated information

Under the hypotheses of [Rao's score test with known information](tendsto-in-distribution-score-statistic.md), let $\hat I_n : \Omega \to \mathbb{R}$ be almost everywhere measurable estimators with $\hat I_n \to I(\theta_0)$ in probability. Then

$$\frac{1}{\hat I_n} \Big(\frac{1}{\sqrt{n}} \sum_{i=0}^{n-1} s_{\theta_0}(X_i)\Big)^2 \to \chi^2_1 \quad \text{in distribution}.$$

Where $\hat I_n(\omega) = 0$ the statistic is $0$ by convention (division by zero); this event has probability tending to $0$ because $I(\theta_0) > 0$.
