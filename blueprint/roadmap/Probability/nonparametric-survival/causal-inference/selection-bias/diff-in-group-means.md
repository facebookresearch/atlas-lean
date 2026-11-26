# Diff In Group Means

Let $\mu$ be a measure on a measurable space $\Omega$, $T \subseteq \Omega$ a treatment event, and $\mu(\cdot \mid A) = \mu(A)^{-1}\, \mu(\cdot \cap A)$ denotes the conditional measure (the zero measure when $\mu(A) = 0$). Integrals of non-integrable functions are taken to be $0$. For an outcome $Y : \Omega \to \mathbb{R}$, the observed difference in group means is

$$\int Y \, d\mu(\cdot \mid T) - \int Y \, d\mu(\cdot \mid T^c) = \mathbb{E}[Y \mid T] - \mathbb{E}[Y \mid T^c].$$
