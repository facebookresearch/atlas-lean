# Moments of the beta distribution

Let $\alpha > 0$ and $\beta > 0$, and let $X$ have the beta distribution $\operatorname{Beta}(\alpha, \beta)$, the probability law on $\mathbb{R}$ with density $x^{\alpha - 1}(1 - x)^{\beta - 1} / B(\alpha, \beta)$ for $0 < x < 1$ and $0$ elsewhere, where $B(a, b) = \Gamma(a)\Gamma(b)/\Gamma(a + b)$ is the beta function. Then for all natural numbers $k$ and $m$ the mixed moment is $\mathbb{E}\bigl[X^k (1 - X)^m\bigr] = B(\alpha + k, \beta + m) / B(\alpha, \beta)$.

## Idea

The beta density is the integrand of the beta function, divided by its total integral. Multiplying it by $x^k (1 - x)^m$ only raises the two exponents, so the integral is again a beta function, now at $(\alpha + k, \beta + m)$, and the moment is the ratio of the two normalising constants. With the recurrence $B(a + 1, b) = \frac{a}{a + b} B(a, b)$ and the symmetry $B(a, b) = B(b, a)$ the ratio becomes explicit: the mean is $\alpha / (\alpha + \beta)$, the second moment is $\alpha(\alpha + 1) / ((\alpha + \beta)(\alpha + \beta + 1))$, and $\mathbb{E}[X(1 - X)] = \alpha\beta / ((\alpha + \beta)(\alpha + \beta + 1))$. The variance $\alpha\beta / ((\alpha + \beta)^2(\alpha + \beta + 1))$ follows; these are the formulas used when the beta law serves as a prior for an unknown proportion.

## Statements

- [Mixed moments of the beta law](integral-pow-mul-one-sub-pow-beta-measur.md)
- [Integrals against the beta law](integral-beta-measure.md): lemma: integrals against the law through its density, used in the proof
- [Beta density integrates to one](integral-beta-pdfreal.md): lemma: normalisation of the density, used in the proof
- [Nonnegativity of the beta density](beta-pdfreal-nonneg.md): basic property of the density
- [Beta-function identity for densities](beta-pdfreal-mul-pow.md): lemma: beta-function identity, used in the proof
- [Recurrence of the beta function in the first argument](beta-add-one-left.md): beta-function identity used for the special cases
- [Symmetry of the beta function](beta-comm.md): beta-function identity used for the special cases
- [Mean of the beta law](integral-id-beta-measure.md): special case: the mean
- [Second moment of the beta law](integral-sq-beta-measure.md): special case: second moment
- [Mean of $X(1 - X)$ under a beta law](integral-mul-one-sub-beta-measure.md): special case: mean of $X(1-X)$
