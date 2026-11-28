# Large-population limit of an individual-based immunotherapy model

**Model.** Cancer cells carry a genotype $g \in \mathcal{G}$ and a phenotype $p \in \mathcal{P}$; T cells have types $z \in \mathcal{Z}$ and cytokines types $w \in \mathcal{W}$. In a population scaled by a carrying-capacity parameter $K$, each individual reproduces, dies, switches or is killed at rates that depend linearly on the rescaled abundances $V_K(t)$ (counts divided by $K$):
- a cancer cell of type $(g,p)$ has reproduction rate $b(p)$ reduced by competition, $b(p) - \sum c_b(p,\tilde p)\,\mathfrak{n}_{(\tilde g,\tilde p)}$ (a negative value acts as extra death), natural death $d(p)$, competitive death $\sum c(p,\tilde p)\,\mathfrak{n}_{(\tilde g,\tilde p)}$, killing by T cells $\sum_z t(z,p)\,\mathfrak{n}_z$, and phenotypic switching to $\tilde p$ at rate $s^g(p,\tilde p) + \sum_w s^g_w(p,\tilde p)\,\mathfrak{n}_w$ (cytokine-induced plasticity without change of genotype); a birth is mutant with probability $\mu_g$, with offspring type law $m$;
- T cells of type $z$ grow at rate $b(z) - d(z) + \sum_{(g,p)} b(z,p)\,\mathfrak{n}_{(g,p)}$ (stimulated by the cancer cells they recognize);
- cytokines decay at rate $d(w)$ and are produced in amounts $\ell^{\mathrm{kill}}_w(z,p)$ and $\ell^{\mathrm{prod}}_w(z,p)$ per T-cell killing event and T-cell stimulation event.

**Proposition (deterministic limit).** If $V_K(0) \to v(0)$ almost surely, then for every $T > 0$,

$$
\mathbb{P}\Bigl(\lim_{K\to\infty}\sup_{0 \le t \le T} |V_K(t) - \mathfrak{n}(t)| = 0\Bigr) = 1,
$$

where $\mathfrak{n}$ is the unique solution with $\mathfrak{n}(0) = v(0)$ of the quadratic system in which, for example,

$$
\frac{d\mathfrak{n}_z}{dt} = \mathfrak{n}_z\Bigl(b(z) - d(z) + \sum_{(g,p)} b(z,p)\,\mathfrak{n}_{(g,p)}\Bigr), \qquad
\frac{d\mathfrak{n}_w}{dt} = -d(w)\,\mathfrak{n}_w + \sum_{(g,p)}\mathfrak{n}_{(g,p)}\sum_{z}\bigl(\ell^{\mathrm{kill}}_w(z,p)\,t(z,p) + \ell^{\mathrm{prod}}_w(z,p)\,b(z,p)\bigr)\mathfrak{n}_z,
$$

and each $\mathfrak{n}_{(g,p)}$ follows the corresponding birth–death–switching–killing balance, with mutational influx $\mathfrak{n}_{(\tilde g,\tilde p)}\,\mu_{\tilde g}\, m((\tilde g,\tilde p),(g,p))\,\bigl\lfloor b(\tilde p) - \sum c_b(\tilde p, \cdot)\,\mathfrak{n}\bigr\rfloor_+$.

## Proof sketch

The model is a multitype Markov jump process whose jump rates are Lipschitz functions of the rescaled state, with jumps of size $1/K$; the classical law of large numbers for density-dependent population processes (Ethier–Kurtz) then gives almost-sure uniform convergence on compact time intervals to the ODE obtained by replacing each rate by its mean drift. The novel ingredients relative to standard individual-based models are environment-dependent phenotype switching driven by cytokines, therapy-induced T-cell killing with cytokine release, and a competition term that lowers reproduction rather than raising death. For finite $K$ the stochastic system can show tumour extinction or relapse from small residual populations, which the deterministic limit cannot.

## Related topics

- [Lotka–Volterra predator–prey model](../../../population-dynamics/lotka-volterra-predator-prey-model/README.md)

## Sources

- Martina Baar, Loren Coquille, Hannah Mayer, Michael Hölzel, Meri Rogava, Thomas Tüting and Anton Bovier, "A stochastic model for immunotherapy of cancer", *Scientific Reports* 6 (2016), 24169, <https://doi.org/10.1038/srep24169>. Preprint version: arXiv:1505.00452 (2015), model definition and Proposition 1, <https://doi.org/10.48550/arXiv.1505.00452>.
