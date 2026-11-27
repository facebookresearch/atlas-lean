# The Gaussian backward channel bounds the Gaussian rate-distortion function from above

Let $\sigma^2 > 0$ and $0 < D < \sigma^2$. Take independent real random variables $\hat X$ with law $N(0, \sigma^2 - D)$ and $Z$
with law $N(0, D)$, and put $X = \hat X + Z$. Then $X$ has law $N(0, \sigma^2)$, the squared-error distortion is
$\mathbb E (X - \hat X)^2 = D$, and

$$I(X; \hat X) = \tfrac12 \log_2 \frac{\sigma^2}{D} \ \text{bits}.$$

Hence the rate-distortion function of the source $N(0, \sigma^2)$ under squared error, the infimum of $I(X; \hat X)$ over joint
laws of $(X, \hat X)$ with source marginal $N(0, \sigma^2)$ and $\mathbb E (X - \hat X)^2 \le D$, is at most
$\tfrac12 \log_2(\sigma^2 / D)$.

The mutual information is symmetric, and $I(\hat X; \hat X + Z) = \tfrac12 \log_2\big(1 + (\sigma^2 - D)/D\big)$ for the Gaussian
input that attains the [capacity of the scalar Gaussian channel](../../channel-coding/scalar-gaussian-channel/capacity-of-the-scalar-additive-gaussian-noise-channel.md)
with power $\sigma^2 - D$ and noise variance $D$.

## Proof depends on

- [Capacity of the scalar additive Gaussian noise channel](../../channel-coding/scalar-gaussian-channel/capacity-of-the-scalar-additive-gaussian-noise-channel.md)

## Sources

- T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd edition, Wiley, 2006, Chapter 10 (the rate-distortion function of a Gaussian source).
