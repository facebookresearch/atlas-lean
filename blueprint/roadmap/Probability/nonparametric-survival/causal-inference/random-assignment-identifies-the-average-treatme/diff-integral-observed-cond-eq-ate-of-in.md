# Identification of the ATE under random assignment

Let $(\Omega, \mu)$ be a probability space, $T \subseteq \Omega$ a measurable treatment event, and $Y_0, Y_1 : \Omega \to \mathbb{R}$ the potential outcomes; $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$ is the observed outcome (consistency), and $\mu(\cdot \mid A) = \mu(A)^{-1}\, \mu(\cdot \cap A)$ denotes the conditional measure (the zero measure when $\mu(A) = 0$). Suppose $Y_0$ and $Y_1$ are measurable and integrable, the indicator $\mathbf{1}_T$ is independent of the pair $(Y_0, Y_1)$, and $0 < \mu(T) < 1$. Then the difference of the observed group means identifies the average treatment effect:

$$\int Y \, d\mu(\cdot \mid T) - \int Y \, d\mu(\cdot \mid T^c) = \int (Y_1 - Y_0) \, d\mu,$$

that is, $\mathbb{E}[Y \mid T] - \mathbb{E}[Y \mid T^c] = \mathbb{E}[Y_1 - Y_0]$.
