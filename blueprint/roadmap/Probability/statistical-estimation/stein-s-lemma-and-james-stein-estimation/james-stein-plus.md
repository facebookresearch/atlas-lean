# Positive-part James–Stein estimator

The positive-part James–Stein estimator of the mean of $\mathcal N_p(\theta, I)$ is

$$\delta^+(x) = \max\Bigl(0,\ 1 - \frac{p - 2}{\|x\|^2}\Bigr) x,$$

Johnstone's draft, equation (2.65): the [James–Stein estimator](james-stein.md) with its shrinkage factor truncated at $0$, so that it never reverses the sign of a coordinate. At $x = 0$ the convention $a / 0 = 0$ gives $\delta^+(0) = 0$.

## Sources

- I. M. Johnstone, *Gaussian Estimation: Sequence and Wavelet Models*, pre-publication draft of 16 September 2019, https://imjohnstone.su.domains/GE_09_16_19.pdf. Numbers refer to that draft.
