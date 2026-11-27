# Inverse probability weighting for the treated mean

Let $\mu$ be a probability measure on $\Omega$, $T$ a measurable event, $X$ a measurable covariate with values in a finite set with measurable singletons and [propensity score](propensity.md) $e$, $Y_0, Y_1 : \Omega \to \mathbb{R}$ potential outcomes with $Y_1$ measurable and integrable, and $Y$ the [observed outcome](observed.md). If treatment is [strongly ignorable](strongly-ignorable.md) given $X$ for $Y_1$, then

$$\mathbb{E}\Big[\mathbf 1_T \frac{Y}{e(X)}\Big] = \mathbb{E}[Y_1].$$

## Sources

- Daniel G. Horvitz and Donovan J. Thompson, *A generalization of sampling without replacement from a finite universe*, J. Amer. Statist. Assoc. 47 (1952), no. 260, 663–685, DOI 10.1080/01621459.1952.10483446.
- Paul R. Rosenbaum, *Model-based direct adjustment*, J. Amer. Statist. Assoc. 82 (1987), no. 398, 387–394, DOI 10.1080/01621459.1987.10478441.
