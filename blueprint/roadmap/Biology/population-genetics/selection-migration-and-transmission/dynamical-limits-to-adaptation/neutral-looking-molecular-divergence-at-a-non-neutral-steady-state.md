# Neutral-looking molecular divergence at a non-neutral steady state

Under the hypotheses of the [zero-fitness-change surface](zero-fitness-change-surface-of-a-rapidly-evolving-population.md) — a non-recombining population of $N$ individuals, mutation rate $U$, distribution of fitness effects $\rho(s)$, and the moderate-selection strong-mutation fixation probability $p_{\mathrm{fix}}(s) \approx e^{T_c s}/N$ with coalescence timescale $T_c$ — let

$$F = N U \int \rho(s)\, p_{\mathrm{fix}}(s)\, ds$$

be the total rate at which selected mutations fix. Selected mutations accumulate at exactly the neutral rate, $F = U$, on the surface

$$\int \tilde\rho(\gamma) \left(e^{\gamma} - 1\right) d\gamma = 0, \qquad \gamma = T_c s,$$

and for a two-effect distribution with scaled effects $\gamma_b$, $-\gamma_d$ and rate ratio $\eta = U_b/U_d$ this is

$$\eta\big|_{F = U} = \frac{1 - e^{-\gamma_d}}{e^{\gamma_b} - 1}. \tag{10}$$

If synonymous mutations are neutral and nonsynonymous ones selected, this is a $dN/dS = 1$ surface. It is distinct from the $v = 0$ surface: $\eta|_{F = U}$ increases monotonically in $\gamma_d$ and decreases monotonically in $\gamma_b$, so unlike the $v = 0$ curves it has no extremum in the space of scaled effects, and as $\gamma_d \to \infty$ its $\gamma_b$ tends to $\log(1 + 1/\eta)$ rather than to $0$.

## Depends on

- [The zero-fitness-change surface of a rapidly evolving population](zero-fitness-change-surface-of-a-rapidly-evolving-population.md)
- [Long-run expected calendar-time rate of neutral substitution](../../../molecular-evolution/long-run-neutral-substitution-rate-law-of-large.md)
- [Nonsynonymous substitution rate per nonsynonymous site (dN)](../../../phylogenetics/codon-substitution-models-and-dn-ds/d-n.md)
- [Synonymous substitution rate per synonymous site (dS)](../../../phylogenetics/codon-substitution-models-and-dn-ds/d-s.md)

## Expansion

Writing $F$ with $p_{\mathrm{fix}}(s) = e^{T_c s}/N$ gives $F = U \int \tilde\rho(\gamma) e^{\gamma} d\gamma$, so $F = U$ is $\int \tilde\rho(\gamma)(e^{\gamma} - 1) d\gamma = 0$; evaluating at the two-effect density yields (10). The two surfaces answer different questions: $v = 0$ weights each fixation by its fitness effect $\gamma$, whereas $F = U$ counts fixations. A population can therefore sit at a steady state in which both mean fitness and the substitution rate look neutral while the dynamics are strongly non-neutral, with beneficial mutations fixing faster than neutrally and deleterious ones slower, exactly cancelling. Because $\gamma_b$ stays bounded away from zero as $\gamma_d$ grows, the heuristic of replacing the coalescence timescale by an effective population size set by strong purifying selection, which works for the $v = 0$ surface at large $\gamma_d$, fails here.

## Sources

- M. J. Melissa and M. M. Desai, "A dynamical limit to evolutionary adaptation", Proceedings of the National Academy of Sciences 121 (2024), e2312845121, Results ("Patterns of Molecular Evolution"), eq. (10), <https://doi.org/10.1073/pnas.2312845121>, PMCID PMC10823227.
