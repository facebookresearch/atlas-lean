# Random assignment, control arm

Let $(\Omega, \mu)$ be a probability space, $T \subseteq \Omega$ a measurable treatment event, and $Y_0, Y_1 : \Omega \to \mathbb{R}$ the potential outcomes; $Y = \mathbf{1}_T Y_1 + \mathbf{1}_{T^c} Y_0$ is the observed outcome (consistency), and $\mu(\cdot \mid A) = \mu(A)^{-1}\, \mu(\cdot \cap A)$ denotes the conditional measure (the zero measure when $\mu(A) = 0$). Suppose $Y_0$ is measurable, the indicator $\mathbf{1}_T$ is independent of $Y_0$, and $\mu(T) < 1$. Then

$$\int Y \, d\mu(\cdot \mid T^c) = \int Y_0 \, d\mu.$$

No integrability is assumed; for non-integrable $Y_0$ both sides take the conventional value $0$.
