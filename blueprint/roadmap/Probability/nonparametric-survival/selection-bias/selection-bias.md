# Selection Bias

Let $\mu$ be a measure on a measurable space $\Omega$, $T \subseteq \Omega$ a treatment event, and $\mu(\cdot \mid A) = \mu(A)^{-1}\, \mu(\cdot \cap A)$ denotes the conditional measure (the zero measure when $\mu(A) = 0$). Integrals of non-integrable functions are taken to be $0$. For the untreated potential outcome $Y_0 : \Omega \to \mathbb{R}$, the selection bias is

$$\int Y_0 \, d\mu(\cdot \mid T) - \int Y_0 \, d\mu(\cdot \mid T^c) = \mathbb{E}[Y_0 \mid T] - \mathbb{E}[Y_0 \mid T^c],$$

the difference between treated and control units in the untreated potential outcome.
