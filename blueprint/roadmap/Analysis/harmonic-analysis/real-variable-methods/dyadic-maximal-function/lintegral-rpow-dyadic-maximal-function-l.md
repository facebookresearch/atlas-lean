# $L^p$ bound for the dyadic maximal function

For $1 < p < \infty$ and every $f \colon \mathbb{R} \to E$ with $\|f\|$ a.e. measurable,

$$\int_{\mathbb{R}} (M_d f)^p \le \Big(\frac{p}{p-1}\Big)^p \int_{\mathbb{R}} \|f\|^p,$$

that is $\|M_d f\|_p \le p' \|f\|_p$ with $p' = p/(p-1)$, where $M_d$ is the [dyadic maximal function](dyadic-maximal-function.md). This is T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, Theorem 3.8, with $\mu = \nu$ the Lebesgue measure on $\mathbb{R}$ (then $M^\mu_d \nu = 1$ and $\omega = \mu$), with the same constant. The source also covers $p = \infty$, where $M_d f \le \|f\|_\infty$ is elementary; that case is not stated. Both integrals are lower Lebesgue integrals in $[0, \infty]$, so there is no integrability hypothesis: when $\int \|f\|^p = \infty$ the bound is trivial.

The source obtains the constant $p'$ from its Marcinkiewicz interpolation theorem (Theorem 3.10). The proof here goes through the [Doob-type inequality](lintegral-rpow-le-lintegral-mul-dyadic-m.md) $X \le p' \int \|f\| (M_d f)^{p-1}$, where $X = \int (M_d f)^p$, and Hölder's inequality with exponents $p$ and $p'$, which give $X \le p' G^{1/p} X^{1/p'}$ with $G = \int \|f\|^p$. To divide by $X^{1/p'}$ one needs $X < \infty$; this comes from the [bound with constant $2^p p/(p-1)$](lintegral-rpow-dyadic-maximal-le-two-rpo.md), which has no such requirement.

## Informally uses

- [Doob-type inequality for the dyadic maximal function](lintegral-rpow-le-lintegral-mul-dyadic-m.md): the estimate combined with Hölder's inequality.
- [$L^p$ bound with constant $2^p p/(p-1)$](lintegral-rpow-dyadic-maximal-le-two-rpo.md): shows $X < \infty$ when $G < \infty$.

## Background

- [Doob's $L^p$ maximal inequality in continuous time](../../../../Probability/martingales/doob-s-maximal-inequalities/lintegral-i-sup-rpow-le.md): the martingale inequality with the same constant $(p/(p-1))^p$.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014 (a secondary source: lecture notes presenting the dyadic theory of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, and of E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993).
