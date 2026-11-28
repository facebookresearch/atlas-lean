# Poisson law of the constitutive splicing master equation

Consider transcription of unspliced RNA $U$ at a deterministic, piecewise continuous rate $\alpha(t) \ge 0$, splicing to $S$ at rate $\beta > 0$ and degradation of $S$ at rate $\gamma > 0$, $\gamma \ne \beta$:

$$\varnothing \xrightarrow{\alpha(t)} U \xrightarrow{\beta} S \xrightarrow{\gamma} \varnothing .$$

Let $P(x_u, x_s; t)$ be the law of the copy numbers given by the chemical master equation and $G(u_u, u_s; t) = \sum_{x} P(x; t) (u_u + 1)^{x_u} (u_s + 1)^{x_s}$ its generating function in shifted variables.

**Theorem.** Starting from zero molecules (or, more generally, from a product of Poisson laws, whose contribution decays deterministically),

$$\ln G(u_u, u_s; t) = \int_0^t \alpha(t - s)\, U_1(u_u, u_s; s)\, ds = \mu_u(t)\, u_u + \mu_s(t)\, u_s,$$

$$U_1(u_u, u_s; s) = u_s \frac{\beta}{\beta - \gamma} e^{-\gamma s} + \Big(u_u - u_s \frac{\beta}{\beta - \gamma}\Big) e^{-\beta s},$$

so that $U$ and $S$ are independent Poisson random variables,

$$P(x_u, x_s; t) = \frac{\mu_u(t)^{x_u} e^{-\mu_u(t)}}{x_u!} \cdot \frac{\mu_s(t)^{x_s} e^{-\mu_s(t)}}{x_s!},$$

with means solving $\mu_u' = \alpha(t) - \beta \mu_u$ and $\mu_s' = \beta \mu_u - \gamma \mu_s$ (closed form for piecewise constant $\alpha$). In particular, for constant $\alpha$ the stationary law is $\mathrm{Poisson}(\alpha/\beta) \otimes \mathrm{Poisson}(\alpha/\gamma)$, and the occupation measure over a uniform sampling window $[0, T]$ is $P(x) = T^{-1}\int_0^T P(x; t)\, dt$, a mixture of product Poissons.

Extensions that keep generating-function tractability:

- bursty transcription, with burst sizes of generating function $M$: $\ln G = \int_0^t \alpha(t - s) [M(U_1(u; s); t - s) - 1]\, ds$;
- a mixture over cell fates with probabilities $w_A$, $1 - w_A$ and driving functions $\alpha_A \ne \alpha_B$: $G = w_A G_A + (1 - w_A) G_B$;
- independent per-molecule technical sampling with generating function $G_{t,i}$ for species $i$: the observed generating function is $G$ evaluated at the composed arguments.

## Depends on

- [Occupation measure of the transient birth–death process](occupation-measure-of-the-transient-birth-death-process.md)

## Expansion

The master equation of a first-order reaction network with zeroth-order input is solved by the method of characteristics: each molecule created at time $t - s$ evolves independently, and $U_1(u; s)$ is the shifted generating-function characteristic of a single unspliced molecule after time $s$ (it is $u_u$ at $s = 0$ and solves the backward linear ODE of the splicing–degradation chain). Superposing independent Poisson immigration of such molecules yields a log-generating function linear in $(u_u, u_s)$, which is the signature of independent Poissons; the coefficients are the means. Since constitutive models force independent Poisson counts (zero spliced–unspliced correlation within a stationary cell population, Fano factor one) in stationary cells, they conflict with widespread transcriptional bursting, whereas bursty transcription yields strictly positive correlations; this motivates the bursty extension.

## Sources

- G. Gorin, M. Fang, T. Chari and L. Pachter, "RNA velocity unraveled", PLoS Computational Biology 18 (2022), e1010492, "The canonical velocity model" and "PGF-tractable models", Eqs. (17)–(20), <https://doi.org/10.1371/journal.pcbi.1010492> (PMC9499228).
