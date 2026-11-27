# Under perfect confounding no estimator is unbiased for the effect

Assume perfect confounding: $\mathrm{batch}(d) = a + b\, \mathrm{cond}(d)$ for every donor $d$, for
real $a$ and $b \ne 0$. Let $\mu$ be any measure on $\Omega$ and $U$ any noise process
$U_i : \Omega \to \mathbb{R}$, one for each cell $i = (d, c)$. Then there is no function
$T : \mathbb{R}^{\delta \times \kappa} \to \mathbb{R}$ with

$$\int T\bigl((Y_i(\omega))_i\bigr)\, d\mu(\omega) = \tau$$

for all real $\mu_0$, $\tau$, $\beta$, where $Y$ are the [observed cell values](obs.md): the
observations, hence the integrals, are the same under $(0, 0, 1)$ and $(a, b, 0)$, whose condition
effects $0$ and $b$ differ. The integral is the Bochner integral, which is $0$ when the integrand is
not integrable; for a probability measure $\mu$ and an integrable $T(Y)$ it is the expectation of
the estimator, so no estimator is unbiased for $\tau$.
