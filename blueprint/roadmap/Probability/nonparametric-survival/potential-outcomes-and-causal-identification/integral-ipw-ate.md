# Identification of the average treatment effect by inverse probability weighting

Let $\mu$ be a probability measure on $\Omega$, $T$ a measurable event, $X$ a measurable covariate with values in a finite set with measurable singletons and [propensity score](propensity.md) $e$, $Y_0, Y_1 : \Omega \to \mathbb{R}$ measurable and integrable potential outcomes, and $Y$ the [observed outcome](observed.md). If treatment is [strongly ignorable](strongly-ignorable.md) given $X$ for the pair $(Y_0, Y_1)$, then

$$\mathbb{E}\Big[\mathbf 1_T \frac{Y}{e(X)} - \mathbf 1_{T^c} \frac{Y}{1 - e(X)}\Big] = \mathbb{E}[Y_1 - Y_0].$$
