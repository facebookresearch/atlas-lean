# Age at diagnosis and per-contact tracing probability on a random tree

**Setting.** An SIR-type epidemic spreads on a rooted random tree: each node has an i.i.d. number $K$ of downstream contacts, with mean $\mathbb E[K] > 1$. While infectious, a node infects each still-susceptible downstream contact at rate $\beta$; it stops being infectious by unobserved recovery at rate $\alpha$, or by diagnosis at rate $\sigma$. A diagnosed node is an *index case* and triggers one-step tracing: each adjacent edge is traced independently with probability $p$, and traced infected contacts are isolated (they do not trigger further tracing). Age always means time since infection. Condition on a major outbreak.

**Age distribution of index cases.** Ignore the effect of tracing on the age structure (an approximation valid when $p$ or the observed fraction $\sigma/(\alpha+\sigma)$ is small). The age-structured density $i(t,a)$ of infected individuals solves $(\partial_t + \partial_a) i = -(\alpha+\sigma) i$ with renewal condition $i(t,0) = \int_0^\infty \theta(a) i(t,a)\, da$, $\theta(a) = \mathbb E[K]\beta e^{-\beta a}$. It grows like $e^{\lambda t}$ with Malthusian rate

$$\lambda = \beta(\mathbb E[K] - 1) - \alpha - \sigma,$$

and the asymptotic age-at-diagnosis density of index cases is

$$\varphi(a) = \beta(\mathbb E[K]-1)\, e^{-\beta(\mathbb E[K]-1)a}, \qquad a \ge 0.$$

The basic reproduction number is $R_0 = \int_0^\infty \theta(a) e^{-(\alpha+\sigma)a}\, da = \mathbb E[K]\beta/(\alpha+\sigma+\beta)$.

**Proposition (tracing probability per downstream contact).** If the focal node becomes an index case at age $a$, a given downstream contact is successfully traced while infected with probability

$$\hat p(a) = p\,\frac{\beta}{\alpha+\sigma-\beta}\big(e^{-\beta a} - e^{-(\alpha+\sigma)a}\big).$$

## Proof sketch

The renewal equation $1 = \int_0^\infty \theta(a) e^{-(\lambda+\alpha+\sigma)a}\, da = \mathbb E[K]\beta/(\lambda+\alpha+\sigma+\beta)$ gives $\lambda$. In the exponential phase the age profile is $e^{-(\lambda+\alpha+\sigma)a} = e^{-\beta(\mathbb E[K]-1)a}$. Diagnosis acts at the constant rate $\sigma$, so index cases have this age profile, normalised. For the proposition, follow one downstream contact during the focal node's infectious period $[0,a)$. It is susceptible with probability $s_1 = e^{-\beta c}$, infected and infectious with $s_2$, removed with $s_3$, where $\dot s_2 = \beta s_1 - (\alpha+\sigma)s_2$ and $s_2(0) = 0$. Solving gives $s_2(a) = \frac{\beta}{\alpha+\sigma-\beta}(e^{-\beta a} - e^{-(\alpha+\sigma)a})$. The edge is then traced with probability $p$.

## Sources

- Augustine Okolie, Johannes Müller and Mirjam Kretzschmar, "Parameter estimation for contact tracing in graph-based models", *Journal of The Royal Society Interface* 20 (2023), 20230409, <https://doi.org/10.1098/rsif.2023.0409>. Preprint version: arXiv:2307.08370 (2023), Sections 2 and 3 and Proposition 4.1, <https://doi.org/10.48550/arXiv.2307.08370>.
