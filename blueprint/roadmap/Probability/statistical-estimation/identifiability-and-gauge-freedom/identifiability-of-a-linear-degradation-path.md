# Identifiability of a linear degradation path

Let $Y_j = \theta_0 + \theta_1 t_j + \varepsilon_j$ for $j = 1, 2$, with known design times $t_1, t_2$, parameter
$\theta = (\theta_0, \theta_1) \in \mathbb{R}^2$, and noise $(\varepsilon_1, \varepsilon_2)$ with a known joint law that does not
depend on $\theta$ and has mean zero and finite second moments, for example independent normal with variance $\sigma^2 > 0$. Then
$\theta$ is identified by the law of $(Y_1, Y_2)$ if and only if $t_1 \ne t_2$. If $t_1 \ne t_2$, equal laws give equal means
$\theta_0 + \theta_1 t_j$, so $\theta_1 = (E Y_2 - E Y_1)/(t_2 - t_1)$ and $\theta_0 = E Y_1 - t_1 \theta_1$. If $t_1 = t_2$, the
distinct parameters $(0, 0)$ and $(-t_1, 1)$ give the same law. An unknown bias in the noise mean would not be identified.
Nonlinear degradation and the use of a prognosis are outside this result.

## Depends on

## Proof depends on

## Sources

- NIST/SEMATECH *e-Handbook of Statistical Methods*, Section 8.4.2.3, degradation models with a parameter drifting linearly in time, <https://www.itl.nist.gov/div898/handbook/apr/section4/apr423.htm>.
