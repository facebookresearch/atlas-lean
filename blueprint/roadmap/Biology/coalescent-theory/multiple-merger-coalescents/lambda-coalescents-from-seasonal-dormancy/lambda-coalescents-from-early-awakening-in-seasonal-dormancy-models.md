# Λ-coalescents from early awakening in seasonal dormancy models

**Model.** Each year has a spring of length $T_N$, a summer, and a winter. Every spring starts with $N$ dormant individuals; individual $i$ wakes at time $\tau_{i,N} \in [0,T_N]$, independently, and from waking on reproduces as a Yule process with birth rate $\lambda_N$. In winter, $N$ individuals chosen uniformly from those alive go dormant and the rest die. This is a Cannings model whose family sizes are the numbers of surviving descendants; let $c_N$ be the pair-coalescence probability per year and $\Psi_{n,N}(k)$ the ancestral partition of a sample of $n$ after $k$ years. The $\Lambda$-coalescent merges any $k$ of $b$ blocks at rate $\int_0^1 y^{k-2}(1-y)^{b-k}\,\Lambda(dy)$.

**Theorem.** (No summer in items 1-2.)
1. (Two-point waking) Let $\mathbb{P}(\tau_{i,N} = 0) = \omega_N = 1 - \mathbb{P}(\tau_{i,N} = T_N)$ with $N\omega_N \to 0$, and $\lambda_N T_N = \beta\log(\kappa N)$ for constants $\kappa, \beta > 0$. Then $\Psi_{n,N}(\lfloor t/c_N\rfloor)$ converges to the star-shaped coalescent if $\beta > 1$, to Kingman's coalescent if $\beta < 1$, and if $\beta = 1$ to the $\Lambda$-coalescent with $y^{-2}\Lambda_\kappa(dy) = \mathbb{P}(Y_\kappa\in dy)/\mathbb{E}[Y_\kappa^2]$, where $\mathbb{P}(Y_\kappa > x) = e^{-x/(\kappa(1-x))}$, $x\in[0,1]$.
2. (Exponentially increasing waking rate) Let $\lambda_N = \lambda$, $T_N - \tau_{i,N} = \zeta_i \wedge T_N$ with $\zeta_i$ i.i.d., $\mathbb{P}(\zeta_1 > y) \sim ce^{-\gamma y}$, and $\log N / T_N \to 0$. With $a = \gamma/\lambda$: if $a \ge 2$ the limit is Kingman's coalescent; if $1 \le a < 2$ it is the Beta$(2-a,a)$-coalescent; if $0 < a < 1$, the processes $(\Psi_{n,N}(\lfloor d\rfloor))_{d\ge 0}$, without time rescaling, converge to the discrete-time $\Xi_a$-coalescent of Schweinsberg (2003), Theorem 4(d).
3. (Characterization) A $\Lambda$-coalescent arises as a limit of rescaled ancestral processes in this family of models if and only if $\Lambda = a_1\delta_0 + a_2\delta_1 + \Lambda'$ with $a_1,a_2 \ge 0$ and $\Lambda'$ on $(0,1)$ with density

$$h(y) = \int_0^\infty \frac{1}{\kappa}\Big(\frac{y}{1-y}\Big)^2 e^{-\frac{y}{\kappa(1-y)}}\,\eta(d\kappa), \qquad \int_0^\infty (1\wedge\kappa^2)\,\eta(d\kappa) < \infty.$$

Equivalently, $h(y) = \frac{y^2}{(1-y)^2}g\big(\frac{y}{1-y}\big)$ for a completely monotone $g$ with $\int_0^\infty g(v)(1\wedge v^2)\,dv < \infty$.

## Depends on

- [Cannings model of a haploid population](../cannings-models/cannings-model.md)
- [Pitman's merger rate](../../coalescents/merger-rate.md)
- [Kingman's coalescent](../../coalescents/merger-rate-dirac-zero.md)
- [The Beta-coalescent measure on the unit interval](../merger-rates-and-beta-coalescents/beta-lambda.md)
- [Merger rates of a coalescent with simultaneous multiple collisions](../../coalescents/xi-coalescents-simultaneous-multiple-collisions.md)

## Proof depends on

- [Möhle–Sagitov conditions for a Λ-coalescent limit](../coalescent-limits-of-cannings-models/mohle-sagitov-lambda.md)

## Expansion

An individual waking at time $0$ instead of $T_N$ founds a Yule family of mean size $e^{\lambda_N T_N}$; when this is of order $N$ ($\beta = 1$) the family is approximately $\kappa NW$ with $W \sim \mathrm{Exp}(1)$, so it occupies the fraction $Y_\kappa = \kappa W/(\kappa W + 1)$ of the next year's founders, producing a multiple merger of that size. Smaller families ($\beta < 1$) only produce pairwise mergers, larger ones ($\beta > 1$) swallow the whole sample. Mixing the scale $\kappa$ over waking times gives the density $h$; the exponential tail of early waking against exponential Yule growth produces power-law family sizes with index $a$, which is the classical route to Beta coalescents. Item 3 follows from Möhle-Sagitov-type criteria for Cannings models.

## Sources

- Fernando Cordero, Adrián González Casanova, Jason Schweinsberg and Maite Wilke-Berenguer, "$\Lambda$-coalescents arising in populations with dormancy", arXiv:2009.09418 (2020), Section 1, Theorems 1.1, 1.2 and 1.4, Proposition 1.5, <https://doi.org/10.48550/arXiv.2009.09418>; published in *Electronic Journal of Probability* 27 (2022) 1–34, as "Λ-coalescents arising in a population with dormancy", <https://doi.org/10.1214/22-EJP739>. Locators follow arXiv v1.
- J. Schweinsberg, "Coalescent processes obtained from supercritical Galton–Watson processes", *Stochastic Process. Appl.* 106 (2003) 107–139, <https://doi.org/10.1016/S0304-4149(03)00028-0>.
