# First-order effect of a tracing delay on the reproduction number: fixed versus exponential delay

**Model.** At the onset of an outbreak in a homogeneous, randomly mixing population (linear branching approximation), infected individuals make infectious contacts at rate $\beta$ and recover at rate $\gamma = \alpha + \sigma$. Here $\sigma = p_{\mathrm{obs}}\gamma$ is the rate of recovery with direct diagnosis, $\alpha = (1-p_{\mathrm{obs}})\gamma$ the rate of undiagnosed recovery, and $p_{\mathrm{obs}}$ the probability that a case becomes an index case. At diagnosis an index case triggers tracing of its infector and infectees, which happens after an independent random delay with density $\phi$ (a generalized function, so a fixed delay is allowed). A traced contact who is still infectious is diagnosed and removed with probability $p$, and traced individuals are again index cases (recursive full tracing). Without tracing, the probability of still being infectious at infection age $a$ is $\widehat\kappa(a) = e^{-(\alpha+\sigma)a}$ and $R_0 = \beta/(\alpha+\sigma)$.

**Theorem.** Assume $\int_0^\varepsilon \phi \to 0$ as $\varepsilon \to 0$. To first order in $p$, the reproduction number of every generation $i \ge 1$ is the same,

$$ R^{(i)} = R_0 - p\,p_{\mathrm{obs}}\Big\{\int_0^\infty \beta^2\,\widehat\kappa(a)\,\big(1 * \phi * (1-\widehat\kappa)\big)(a)\,da + \int_0^\infty \beta\,\widehat\kappa(a)\,\big((1-\widehat\kappa) * \phi\big)(a)\,da\Big\} + O(p^2), $$

where the first term is backward tracing and the second forward tracing. In particular:

1. Fixed delay $T$, $\phi = \delta_T$:

$$ R_{ct} = R_0 - \tfrac12\,p\,p_{\mathrm{obs}}\,e^{-(\alpha+\sigma)T}\,R_0(R_0+1) + O(p^2). $$

2. Exponential delay with mean $T$, $\phi(a) = e^{-a/T}/T$:

$$ R_{ct} = R_0 - \tfrac12\,p\,p_{\mathrm{obs}}\,\frac{R_0(R_0+1)}{1 + T(\alpha+\sigma)} + O(p^2). $$

In both cases the effect of tracing depends on the delay only through $T(\alpha+\sigma)$, the mean delay divided by the mean infectious period. Since $1/(1+x) > e^{-x}$ for $x > 0$, a random (exponential) delay reduces $R$ more than a fixed delay with the same mean: its effect decays polynomially in $T$ instead of exponentially.

## Expansion

Tracing makes the removal hazard of an individual depend on the history of its infector and infectees. The probability $\kappa_i(a)$ of being infectious at age $a$ in generation $i$ satisfies exact delay-integral equations; expanding in $p$ around $\widehat\kappa$ separates the two routes. Backward tracing works through infectees diagnosed earlier, and forward tracing through the infector's diagnosis. With $\phi = \delta_T$ the convolutions are shifts, so the forward term is $\widehat\kappa(T)\int_0^\infty \beta\widehat\kappa(1-\widehat\kappa) = \tfrac12 R_0\widehat\kappa(T)$ and the backward term is $\tfrac12 R_0^2\widehat\kappa(T)$, which sum to the stated formula. For the exponential delay the same integrals equal $R_0/(2(1+T(\alpha+\sigma)))$ and $R_0^2/(2(1+T(\alpha+\sigma)))$, and $1/(1+x)$ is the $[0/1]$ Padé approximant of $e^{-x}$. The approximation is accurate for moderate $p$ (around $p \le 0.3$ in simulations of the stochastic process) and ignores depletion of susceptibles.

## Sources

- Johannes Müller and Bendix Koopmann, "The effect of delay on contact tracing", arXiv:1610.07054 (2016): Section 2, Proposition 2.8 and Remark 2.9 (first-order full tracing), Proposition 2.10 (fixed delay), Proposition 2.11 (exponential delay). <https://doi.org/10.48550/arXiv.1610.07054> Published version: Mathematical Biosciences 282 (2016) 204–214, <https://doi.org/10.1016/j.mbs.2016.10.010>.
