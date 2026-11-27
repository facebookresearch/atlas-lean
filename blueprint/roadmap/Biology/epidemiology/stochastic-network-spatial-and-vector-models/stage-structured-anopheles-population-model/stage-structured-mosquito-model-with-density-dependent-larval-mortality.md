# Stage-structured mosquito model with density-dependent larval mortality

**Setting.** Let $E(t)$, $L(t)$, $P(t)$, $M(t) \ge 0$ be the numbers of early larval instars (eggs and instars 1–2), late larval instars (instars 3–4), pupae and adult females in one breeding site. Adult females lay $\beta$ eggs per day ([oviposition rate](oviposition-rate-from-the-gonotrophic-cycle.md)); the stages have mean durations $d_E, d_L, d_P > 0$; pupae and adults die at constant rates $\mu_P, \mu_M > 0$; half of emerging adults are female. Crowding acts only on the feeding larval stages, linearly in total larval density, through the death rates

$$\mu_E(E,L) = \mu_E^0\left(1 + \frac{E + L}{K}\right), \qquad \mu_L(E,L) = \mu_L^0\left(1 + \gamma\,\frac{E + L}{K}\right),$$

with low-density rates $\mu_E^0, \mu_L^0 > 0$, carrying capacity $K > 0$ (rainfall-dependent in the source) and $\gamma > 0$ the relative strength of density dependence on late instars. The dynamics are

$$
\begin{aligned}
\frac{dE}{dt} &= \beta M - \frac{E}{d_E} - \mu_E(E,L)\,E, &
\frac{dL}{dt} &= \frac{E}{d_E} - \frac{L}{d_L} - \mu_L(E,L)\,L, \\
\frac{dP}{dt} &= \frac{L}{d_L} - \frac{P}{d_P} - \mu_P P, &
\frac{dM}{dt} &= \frac{P}{2 d_P} - \mu_M M .
\end{aligned}
$$

**Proposition.**

1. The closed orthant $\{E, L, P, M \ge 0\}$ is forward invariant, and $0$ is an equilibrium.
2. Conditional on larval densities, the probabilities of surviving each aquatic stage are

$$s_E = \frac{1}{1 + d_E\,\mu_E(E,L)}, \qquad s_L = \frac{1}{1 + d_L\,\mu_L(E,L)}, \qquad s_P = \frac{1}{1 + d_P\,\mu_P},$$

each decreasing in total larval density (for $s_E, s_L$).
3. The time spent from egg to emergence is a sum of three independent exponential durations, so its law is hypoexponential (approximately gamma-shaped), not exponential.

## Depends on

- [Oviposition rate from the gonotrophic cycle](oviposition-rate-from-the-gonotrophic-cycle.md)

## Expansion

(1): each right-hand side is non-negative when its own variable is zero and the others are non-negative. (2): an individual in stage $X$ leaves by development at rate $1/d_X$ or by death at rate $\mu_X$, so it develops with probability $(1/d_X)/(1/d_X + \mu_X)$. (3) is the motivation for splitting the aquatic phase: a single compartment would allow implausibly short development times. Linear density dependence in larval numbers corresponds to death rate proportional to larval biomass in more detailed models, and was preferred to logistic or quadratic forms for parsimony after fitting semi-field larval survival data with staggered introductions. Larval source management acts by lowering $K$, larvicides by raising $\mu_E^0, \mu_L^0$, and adult interventions by raising $\mu_M$ or lowering $\beta$.

## Sources

- M. T. White, J. T. Griffin, T. S. Churcher, N. M. Ferguson, M.-G. Basáñez, A. C. Ghani, "Modelling the impact of vector control interventions on *Anopheles gambiae* population dynamics", Parasites & Vectors 4 (2011) 153, Methods, "Mosquito population dynamics" (Eq. (1)) and "Density-dependent larval mortality" (Eq. (7)), <https://doi.org/10.1186/1756-3305-4-153> (PMC3158753).
