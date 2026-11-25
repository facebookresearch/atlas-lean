# Kaplan–Meier survival estimate

For [grouped right-censored data](censored-data.md) and $t \in \mathbb{R}$, the Kaplan–Meier estimate of the survival function is

$$\hat S(t) = \prod_{j : t_j \le t} \Big(1 - \frac{d_j}{n_j}\Big),$$

the product of the [Kaplan–Meier factors](km-factor.md) at the observation times up to $t$ (an empty product, $1$, for $t < t_1$).

## Sources

- Edward L. Kaplan and Paul Meier, *Nonparametric estimation from incomplete observations*, J. Amer. Statist. Assoc. 53 (1958), no. 282, 457–481, DOI 10.1080/01621459.1958.10501452.
