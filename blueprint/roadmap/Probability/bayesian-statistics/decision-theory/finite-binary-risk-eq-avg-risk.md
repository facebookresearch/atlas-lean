# Finite unequal-cost binary risk

Let $\mathcal{X}$ be a finite set (with measurable singletons), and let $P_0, P_1 : \mathcal{X} \to [0, \infty)$ be probability tables, $\sum_x P_0(x) = \sum_x P_1(x) = 1$. Let $\delta : \mathcal{X} \to [0, 1]$ be a randomized test, $0 < \pi < 1$, and $c_{\mathrm{FP}}, c_{\mathrm{FN}} > 0$. Take the parameter $\theta \in \{0, 1\}$ (negative $= 0$, positive $= 1$), decisions in $\{0, 1\}$, and

- the loss $\ell(\theta, y) = 0$ if $y = \theta$, $\ell(0, 1) = c_{\mathrm{FP}}$, $\ell(1, 0) = c_{\mathrm{FN}}$;
- the experiment $\theta \mapsto \sum_x P_\theta(x)\, \delta_x$;
- the decision kernel sending $x$ to the Bernoulli law $(1 - \delta(x))\, \delta_0 + \delta(x)\, \delta_1$;
- the prior $(1 - \pi)\, \delta_0 + \pi\, \delta_1$.

Then the average risk $R$ of this decision kernel, $R = \int \int \ell(\theta, y)\, d(\kappa \circ P_\theta)(y)\, d\pi(\theta)$, is finite and

$$R = (1 - \pi)\, c_{\mathrm{FP}} \sum_{x} P_0(x)\, \delta(x) + \pi\, c_{\mathrm{FN}} \sum_{x} P_1(x)\, \bigl(1 - \delta(x)\bigr).$$
