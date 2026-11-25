# Att

Let $\mu$ be a measure on a measurable space $\Omega$, $T \subseteq \Omega$ a treatment event, and $\mu(\cdot \mid A) = \mu(A)^{-1}\, \mu(\cdot \cap A)$ denotes the conditional measure (the zero measure when $\mu(A) = 0$). Integrals of non-integrable functions are taken to be $0$. For potential outcomes $Y_0, Y_1 : \Omega \to \mathbb{R}$, the average treatment effect on the treated is

$$\mathrm{ATT} = \int (Y_1 - Y_0) \, d\mu(\cdot \mid T) = \mathbb{E}[Y_1 - Y_0 \mid T].$$
