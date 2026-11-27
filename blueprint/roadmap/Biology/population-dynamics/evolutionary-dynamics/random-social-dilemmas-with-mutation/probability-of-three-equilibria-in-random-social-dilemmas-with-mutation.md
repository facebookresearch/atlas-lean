# Probability of three equilibria in random social dilemmas with mutation

**Model.** In an infinite population playing a two-player game with strategies cooperate (C, frequency $x$) and defect (D), payoffs $a_{11} = 1$ (C vs C), $a_{12} = S$ (C vs D), $a_{21} = T$ (D vs C), $a_{22} = 0$, and symmetric mutation probability $q \in [0, 1/2]$ between the two strategies, the replicator–mutator dynamics reduce to

$$\dot x = (T+S-1)x^3 + \big(1 - T - 2S + q(S - 1 - T)\big)x^2 + \big(S + q(T-S)\big)x .$$

Equilibria are the roots in $[0,1]$; $x = 0$ is always one, so there are $1$, $2$ or $3$ equilibria. Random social dilemmas draw the payoffs uniformly:

- Prisoner's Dilemma (PD): $T \sim U(1,2)$, $S \sim U(-1,0)$;
- Stag Hunt (SH): $T \sim U(0,1)$, $S \sim U(-1,0)$;
- Snowdrift (SD): $T \sim U(1,2)$, $S \sim U(0,1)$; Harmony (H): $T \sim U(0,1)$, $S \sim U(0,1)$.

Write $p_k^{G}$ for the probability that game $G$ has $k$ equilibria.

**Known baseline.** $p_2^{SD} = p_2^{H} = 1$; $p_2^{SH} = \frac{q}{2(1-q)}$; $p_2^{PD} = \frac{3q}{2(1-q)}$ for $0 < q \le 1/3$ and $p_2^{PD} = 3 - \frac{1}{2q(1-q)}$ for $1/3 \le q \le 1/2$.

**Theorem (three equilibria).** For $0 < q < 1/2$, let

$$D = \Big\{(x,y) : -1 < x < 0,\ -\tfrac{x^2}{4q} - q < y < -q\Big\}.$$

1. $p_3^{SH} = \frac{1}{1-2q}\,\mathrm{Area}(D \cap D_1)$, where $D_1$ is the quadrilateral with vertices $(-1,-1)$, $(-(1-q), -q)$, $(0,0)$, $(-q, -(1-q))$; explicitly, for $4/9 < q < 1/2$,

$$p_3^{SH} = 1 - \frac{q}{2(1-q)} - \frac{8\sqrt{q}\,(1-2q)^2}{3(1-q)^3},$$

with a longer closed form (involving $\sqrt q$ and $\sqrt{1-2q}$) for $0 < q \le 4/9$.
2. $p_3^{PD} = \frac{1}{1-2q}\,\mathrm{Area}(D \cap D_2)$, where $D_2$ is the triangle with vertices $(-q, -(1-q))$, $(0, -\frac{1-2q}{1-q})$, $(0,0)$; explicitly, for $4/9 < q < 1/2$,

$$p_3^{PD} = \frac{(1-2q)^2}{2q(1-q)},$$

with separate closed forms on $0 \le q \le \frac{3-\sqrt5}{2}$ and $\frac{3-\sqrt5}{2} < q \le 4/9$, and in all cases $p_3^{PD} \le \frac{q}{2(1-q)}$.

Together with $p_1 = 1 - p_2 - p_3$ this gives the full law, mean and variance of the number of equilibria as functions of the mutation probability.

## Proof sketch

Dividing out the root $x = 0$ leaves a quadratic whose coefficients are affine in $(T,S)$. In the variables $X = (1-q)(T-1) + qS$ and $Y = q(T-1) + (1-q)S$ (a linear change of variables with Jacobian $1-2q$) the condition "two distinct roots in $(0,1)$" becomes $(X,Y) \in D$, a region bounded by a parabola, while the uniform payoff square maps to the polygon $D_1$ (SH) or $D_2$ (PD). Computing the area of the intersection gives the piecewise formulas; the breakpoints in $q$ are where the parabola crosses polygon vertices.

## Sources

- Manh Hong Duong and The Anh Han, "Statistics of the number of equilibria in random social dilemma evolutionary games with mutation", *The European Physical Journal B* 94 (2021), 171, <https://doi.org/10.1140/epjb/s10051-021-00181-0>. Preprint version: arXiv:2107.06025 (2021), Theorems 1.1–1.2, Propositions 2.2 and 2.4, Lemma 2.5, Theorems 2.3 and 2.6, <https://doi.org/10.48550/arXiv.2107.06025>.
