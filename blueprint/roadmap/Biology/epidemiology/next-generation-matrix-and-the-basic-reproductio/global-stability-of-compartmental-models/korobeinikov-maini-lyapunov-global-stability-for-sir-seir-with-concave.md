# Local stability for SIRS and SEIRS models with concave incidence

Korobeinikov and Maini (2005) consider incidence rates $f(S, I, N)$ with $f(S, 0, N) = f(0, I, N) = 0$ (2.1), $\partial f/\partial S > 0$ and $\partial f/\partial I > 0$ for $S, I > 0$ (2.2), and concavity in the number of infectives, $\partial^2 f/\partial I^2 \le 0$ (2.3), with $R_0 = \frac{1}{\delta + \mu}\frac{\partial f}{\partial I}$ at the infection-free state (Eq. (3.5)). For the SIRS model (3.1),

$$\dot S = (\alpha + \mu)N - f(S, I, N) - \alpha I - (\alpha + \mu)S, \qquad \dot I = f(S, I, N) - (\delta + \mu)I,$$

with birth and death rate $\mu$, recovery rate $\delta$ and loss-of-immunity rate $\alpha$, they prove: under (2.1)–(2.3), if $R_0 > 1$ there is a unique positive endemic equilibrium in addition to the infection-free one (Lemma 3.3), and it is asymptotically stable; if $R_0 \le 1$ there is no endemic equilibrium and the infection-free equilibrium is asymptotically stable (Theorem 3.4). The same holds for the SEIRS model (3.6) with a latent class, with $R_0$ taken at the infection-free state of that model (Lemma 3.8 and Theorem 3.9). Global stability for incidence of product form $h(S)g(I)$ in the SIR and SEIR models (Theorem 4.1 of the source) is stated, under adapted incidence hypotheses, by the Korobeinikov–Maini theorems for the [SIR endemic case](../../global-stability-with-nonlinear-incidence/sir-endemic-globally-stable.md), the [SIR disease-free case](../../global-stability-with-nonlinear-incidence/sir-disease-free-globally-stable.md), the [SEIR endemic case](../../global-stability-with-nonlinear-incidence/seir-endemic-globally-stable.md) and the [SEIR disease-free case](../../global-stability-with-nonlinear-incidence/seir-disease-free-globally-stable.md), and is not restated here.

## Expansion

1. The incidence hypotheses (2.1)–(2.3) and $R_0$ from the linearization at the infection-free state.
2. Lemma 3.1 (the slope inequality $\partial f/\partial I < \delta + \mu$ at an endemic equilibrium) and Lemma 3.3 (existence and uniqueness of the endemic equilibrium for $R_0 > 1$, its absence for $R_0 \le 1$).
3. Theorem 3.4: the Jacobian of (3.1) at each equilibrium and the resulting asymptotic stability.
4. The SEIRS analogue: Lemmas 3.7 and 3.8 and Theorem 3.9.
5. As a separate statement, Theorem 4.1 of the source under its own conditions (2.1)–(2.3) with a finite slope $g'(0)$, which differ from the adapted hypotheses of the [SIR endemic case](../../global-stability-with-nonlinear-incidence/sir-endemic-globally-stable.md) in both directions.

## Sources

- A. Korobeinikov and P. K. Maini, Non-linear incidence and stability of infectious disease models, Math. Med. Biol. 22 (2005), 113–128, conditions (2.1)–(2.3), Eq. (3.5), Lemmas 3.1, 3.3, 3.7, Theorems 3.4 and 3.9. <https://doi.org/10.1093/imammb/dqi001>
