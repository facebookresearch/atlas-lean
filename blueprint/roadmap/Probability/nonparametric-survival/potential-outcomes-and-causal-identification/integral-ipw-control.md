# Inverse probability weighting for the control mean

Let $\mu$ be a probability measure on $\Omega$, $T$ a measurable event, $X$ a measurable covariate with values in a finite set with measurable singletons and [propensity score](propensity.md) $e$, $Y_0, Y_1 : \Omega \to \mathbb{R}$ potential outcomes with $Y_0$ measurable and integrable, and $Y$ the [observed outcome](observed.md). If treatment is [strongly ignorable](strongly-ignorable.md) given $X$ for $Y_0$, then

$$\mathbb{E}\Big[\mathbf 1_{T^c} \frac{Y}{1 - e(X)}\Big] = \mathbb{E}[Y_0].$$
