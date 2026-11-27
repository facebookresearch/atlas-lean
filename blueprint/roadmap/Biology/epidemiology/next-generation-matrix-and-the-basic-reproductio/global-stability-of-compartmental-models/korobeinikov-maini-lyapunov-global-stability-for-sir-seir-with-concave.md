# Global stability for SIR and SEIR models with concave incidence

Korobeinikov and Maini (2005) consider incidence rates $f(S, I, N)$ with $f(S, 0, N) = f(0, I, N) = 0$ (2.1), $\partial f/\partial S > 0$ and $\partial f/\partial I > 0$ for $S, I > 0$ (2.2), and concavity in the number of infectives, $\partial^2 f/\partial I^2 \le 0$ (2.3), with $R_0 = \frac{1}{\delta + \mu}\frac{\partial f}{\partial I}$ at the infection-free state (Eq. (3.5)). For incidence of product form $f = h(S)g(I)$ satisfying (2.1)–(2.3), and the normalized SIR model $\dot S = \mu - h(S)g(I) - \mu S$, $\dot I = h(S)g(I) - (\delta + \mu)I$ (and the SEIR model (4.2) with latency rate $\theta$), their Theorem 4.1 states: if $R_0 > 1$ the endemic equilibrium is globally asymptotically stable in the positive orthant, so that every solution with all components positive at time $0$ converges to it (the face $I = 0$, and for SEIR the face $E = I = 0$, is invariant), and if $R_0 \le 1$ there is no positive equilibrium and the infection-free equilibrium is globally asymptotically stable. The proof uses the Lyapunov function (4.4), $V = S - h(S^*)\int_a^S \frac{d\tau}{h(\tau)} + B\bigl(I - g(I^*)\int_a^I\frac{d\tau}{g(\tau)}\bigr) + C(E - E^*\ln E)$, which reduces to $S - S^*\ln S + B(I - I^*\ln I) + C(E - E^*\ln E)$ for bilinear incidence. For general concave $f$ the source proves the corresponding local statements for the SIRS and SEIRS models (Theorem 3.4 and its SEIRS analogue), and it notes that for convex incidence the positive equilibrium need not be unique.

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Expansion

1. The incidence hypotheses (2.1)–(2.3), the product form $h(S)g(I)$, and $R_0$ from the linearization at the infection-free state.
2. Existence and uniqueness of the endemic equilibrium for $R_0 > 1$ from concavity (Lemma 3.3), and its absence for $R_0 \le 1$.
3. The Lyapunov function (4.4) for the SIR and SEIR models, its global minimum at the endemic equilibrium, and the sign of its derivative, completed by [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md).
4. The infection-free case $R_0 \le 1$.
5. Local stability for general concave incidence in the SIRS and SEIRS models (Section 3), and the source's discussion of convex incidence.

## Sources

- A. Korobeinikov and P. K. Maini, Non-linear incidence and stability of infectious disease models, Math. Med. Biol. 22 (2005), 113–128, conditions (2.1)–(2.3), Eq. (3.5), Theorem 3.4 and Theorem 4.1. <https://doi.org/10.1093/imammb/dqi001>
