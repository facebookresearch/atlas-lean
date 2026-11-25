# Integrals against the beta law

Let $\alpha, \beta > 0$, let $\operatorname{Beta}(\alpha, \beta)$ be the beta law on $\mathbb{R}$
and $f_{\alpha, \beta}$ its density (as on [the density identity page](beta-pdfreal-mul-pow.md)).
For every $g : \mathbb{R} \to \mathbb{R}$,

$$\int g \, d\operatorname{Beta}(\alpha, \beta) = \int_{\mathbb{R}} f_{\alpha, \beta}(x)\, g(x)\, dx .$$

No integrability hypothesis is needed: $g$ is integrable for the beta law exactly when
$f_{\alpha, \beta}\, g$ is Lebesgue integrable, and otherwise both integrals are $0$ by convention.
