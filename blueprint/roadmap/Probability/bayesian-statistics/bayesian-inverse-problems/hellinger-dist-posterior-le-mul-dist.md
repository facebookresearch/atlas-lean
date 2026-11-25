# Well-posedness: the posterior is locally Lipschitz in the data in Hellinger distance

Let the unknown $u$ live in a finite-dimensional real normed space with its Borel σ-algebra and prior probability measure $\mu_0$, and the data $y$ in a seminormed group; let $r \in \mathbb{R}$.
Let the potential $\Phi(u; y)$ be continuous in $u$ and satisfy, for all $u$ and all $\|y\|, \|y'\| \le r$,

$$
\Phi(u; y) \ge -M_1(\|u\|), \qquad |\Phi(u; y) - \Phi(u; y')| \le M_2(\|u\|) \, \|y - y'\|,
$$

with $M_1$, $M_2$ nondecreasing and $\exp(M_1(\|u\|))(1 + M_2(\|u\|)^2)$ integrable under $\mu_0$. Then
there is $C$ such that

$$
d_{\mathrm{Hell}}(\mu^y, \mu^{y'}) \le C \, \|y - y'\| \qquad \text{for all } \|y\|, \|y'\| \le r .
$$

So, unlike the classical inverse problem, the Bayesian inverse problem is well posed: small changes
in the data give small changes in the posterior, and hence, by the
[control of expectations](../../convergence-of-measures/hellinger-distance/norm-integral-sub-integral-le-hellinger.md), in posterior means.

This is Theorem 4.5 of Dashti and Stuart with $X' = X$ finite-dimensional and Assumptions 4.2 at the
fixed radius $r$. For Gaussian noise and a continuous forward map with $|G(u)| \le M(\|u\|)$ one can
take $M_1 = 0$. For example, the standard Gaussian prior on $\mathbb R$ with forward map $G = \sin$ and misfit $\Phi(u; y) = (y - \sin u)^2/2$ satisfies the hypotheses with $M_1 = 0$ and $M_2 = r + 1$.

## Sources

- Masoumeh Dashti and Andrew M. Stuart, *The Bayesian approach to inverse problems*, in *Handbook of Uncertainty Quantification*, Springer (2017), 311–428, DOI 10.1007/978-3-319-12385-1_7; numbering of arXiv:1302.6989v4 (2015), Assumptions 4.2 and Theorem 4.5.
