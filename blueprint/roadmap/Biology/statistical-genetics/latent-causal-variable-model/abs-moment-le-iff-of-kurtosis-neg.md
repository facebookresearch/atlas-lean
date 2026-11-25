# Uncentred moment comparison is reversed for negative excess kurtosis

In a [latent causal variable model](model.md) on a probability measure $P$, suppose that the [excess kurtosis](kurtosis.md) satisfies $\kappa_\pi < 0$ and that $q_1 q_2 \ne 0$. Then

$$\Bigl|\int \alpha_1 \alpha_2^3 \, dP\Bigr| \le \Bigl|\int \alpha_1^3 \alpha_2 \, dP\Bigr| \iff q_1^2 \le q_2^2,$$

where $\alpha_1, \alpha_2$ are the [marginal effects](alpha1.md). So the comparison of uncentred moments orders $q_1^2$ and $q_2^2$ as expected only when $\kappa_\pi > 0$, whereas the [centred comparison](abs-centred-moment-le-iff.md) needs only $\kappa_\pi \ne 0$.
