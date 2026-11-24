# Scaled compensated increment of the density paths

For real $\beta$, $\gamma$ and paths $X_N(\omega) : \mathbb{R} \to \mathbb{R}^2$, the scaled
compensated increment is

$$
M_N(\omega)(t) = \sqrt N\, \Bigl(X_N(\omega)(t) - X_N(\omega)(0) -
\int_0^t F\bigl(X_N(\omega)(s)\bigr)\, ds\Bigr),
$$

with the [drift](drift.md) $F$ and the Bochner integral, which is $0$ when the integrand is not
integrable. For the SIR chain in its random time-change representation it is the scaled compensated
Poisson martingale

$$
\sum_\ell \ell\, N^{-1/2} \Bigl(Y_\ell\Bigl(N \int_0^t \lambda_\ell(X_N)\Bigr) -
N \int_0^t \lambda_\ell(X_N)\Bigr),
$$

with unit Poisson processes $Y_\ell$; for a general family of paths it need not be a martingale.
