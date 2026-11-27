# The zero-fitness-change surface of a rapidly evolving population

**Model.** A population of $N$ haploid individuals, without recombination in the region considered, acquires mutations at total rate $U$ per individual per generation. A new mutation has fitness effect $s$ drawn from a distribution of fitness effects $\rho(s)$ (beneficial for $s > 0$, deleterious for $s < 0$) that is treated as fixed over the relevant timescales. A mutation of effect $s$ adds $s$ to log fitness, and the expected offspring number of an individual of fitness $X$ is $e^{X - \bar X}$. Let $v$ be the average rate of change of mean fitness and $p_{\mathrm{fix}}(s)$ the fixation probability of a new mutation of effect $s$.

**Statement** (Melissa and Desai 2024, eqs. (1), (2), (4), (5), (6)). The rate of fitness change is

$$v = N U \int \rho(s)\, s\, p_{\mathrm{fix}}(s)\, ds. \tag{1}$$

In the moderate-selection, strong-mutation regime the fixation probability is, for positive and negative $s$ alike,

$$p_{\mathrm{fix}}(s) \approx \frac{e^{T_c s}}{N}, \tag{2}$$

where $T_c \approx T_2/2$ is half the mean pairwise coalescence time. Writing the scaled effect $\gamma = T_c s$ and $\tilde\rho$ for its density, the boundary $v = 0$ between adaptation and fitness decline is

$$\int \tilde\rho(\gamma)\, \gamma\, e^{\gamma}\, d\gamma = 0. \tag{4}$$

For a two-effect distribution with scaled beneficial effect $\gamma_b$, scaled deleterious effect $-\gamma_d$ ($\gamma_b, \gamma_d > 0$) and ratio $\eta = U_b/U_d$ of beneficial to deleterious mutation rates, this gives

$$\eta\big|_{v = 0} = \frac{\gamma_d e^{-\gamma_d}}{\gamma_b e^{\gamma_b}}, \tag{5}$$

and for exponentially distributed effects with means $\gamma_b \in (0, 1)$ (required for the beneficial integral to converge) and $\gamma_d > 0$,

$$\eta\big|_{v = 0} = \frac{\gamma_d}{\gamma_b} \frac{(1 - \gamma_b)^2}{(1 + \gamma_d)^2}. \tag{6}$$

## Depends on

- [Long-run expected calendar-time rate of neutral substitution](../../../molecular-evolution/long-run-neutral-substitution-rate-law-of-large.md)

## Expansion

Substituting (2) into (1) and changing variables to $\gamma$ removes $N$, $U$ and the overall scale, leaving (4): on the boundary the exponentially weighted mean scaled effect vanishes. Equation (5) follows by evaluating (4) at $\tilde\rho(\gamma) = \frac{\eta}{1 + \eta}\delta(\gamma - \gamma_b) + \frac{1}{1 + \eta}\delta(\gamma + \gamma_d)$ and solving for $\eta$. Two features follow from (5). When both effects are weak ($\gamma_b, \gamma_d \ll 1$) it reduces to $\eta \approx \gamma_d/\gamma_b$, that is $U_b s_b = U_d s_d$, the neutral-accumulation balance in which every mutation fixes with probability $1/N$; this is an upper bound on the actual boundary. And the right-hand side is not monotone in $\gamma_d$: $\gamma_d e^{-\gamma_d}$ is maximized at $\gamma_d^* = 1$, so deleterious mutations do the most damage when their scaled effect is of order the coalescence timescale, being too weak to matter below it and too efficiently purged above it. At fixed $\eta$ the population always adapts when $\gamma_b > \gamma_b^*$, where $\gamma_b^* e^{\gamma_b^*} = 1/(e\eta)$. Equation (2) differs from the independent-loci formula $p_{\mathrm{fix}}(s) = (2T_c/N) \cdot 2s/(1 - e^{-4T_c s})$, which ignores the linked selection that this regime is built around.

## Sources

- M. J. Melissa and M. M. Desai, "A dynamical limit to evolutionary adaptation", Proceedings of the National Academy of Sciences 121 (2024), e2312845121, Model and Results, eqs. (1)–(6), <https://doi.org/10.1073/pnas.2312845121>, PMCID PMC10823227.
