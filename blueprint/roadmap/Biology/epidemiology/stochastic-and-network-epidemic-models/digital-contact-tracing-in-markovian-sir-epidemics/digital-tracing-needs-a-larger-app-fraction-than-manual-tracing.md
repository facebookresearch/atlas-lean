# Digital tracing needs a larger app fraction than the manual tracing probability

In the Markovian SIR epidemic with contact rate $\beta$, recovery rate $\gamma$, diagnosis rate $\delta$ and $R_0 = \beta/(\gamma+\delta) > 1$, compare digital tracing with app fraction $\pi$ to manual tracing in which each contact of a diagnosed case is traced independently with probability $p$. Let $\pi_c$ be the app fraction with $R_D = 1$ and $p_c$ the manual tracing probability at which the manual reproduction number equals $1$.

1. **Critical fractions.**

    $$\pi_c > p_c = \frac{\beta - (\gamma+\delta)}{\beta - \gamma} .$$

2. **Individual reproduction number.** With $f(\pi)$ as in the digital-tracing reproduction number, set

    $$R^{(\mathrm{ind})}_D = \frac{\pi f(\pi)}{1 - \pi + \pi f(\pi)} + (1-\pi)\frac{\beta}{\gamma+\delta} .$$

    Unlike $R_D$, which can increase with $\pi$, $R^{(\mathrm{ind})}_D$ is strictly decreasing in $\pi \in [0,1]$.

3. **Common threshold.** $R_D = R^{(\mathrm{ind})}_D = 1$ at $\pi = \pi_c$; both exceed $1$ for $\pi < \pi_c$ and both are below $1$ for $\pi > \pi_c$.

## Depends on

- [Reproduction number of app-based digital contact tracing](reproduction-number-of-app-based-digital-contact-tracing.md)

## Expansion

Digital tracing reaches a contact only if both ends use the app, so a fraction $\pi$ of app-users traces only a fraction $\pi^2$ of transmission pairs. Manual tracing with probability $p$ reaches a fraction $p$ of the contacts of every diagnosed case. The macro-individual reproduction number counts components rather than people, so it need not decrease with $\pi$. Converting it to the mean number infected per individual restores monotonicity without moving the threshold.

## Sources

- Tom Britton and Dongni Zhang, "Epidemic models with digital and manual contact tracing", Advances in Applied Probability 57 (2025), 1430–1455, <https://doi.org/10.1017/apr.2025.15>; numbering as in arXiv:2211.12869: Section 3 (main results: the limit-process proposition and its corollary for digital tracing, and the three theorems comparing critical fractions and the individual reproduction number).
