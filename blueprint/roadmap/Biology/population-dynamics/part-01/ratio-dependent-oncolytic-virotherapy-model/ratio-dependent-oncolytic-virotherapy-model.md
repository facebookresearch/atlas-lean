# Ratio-dependent oncolytic virotherapy model

**Model.** Let $X(t)$ and $Y(t)$ be the numbers of uninfected and virus-infected tumour cells. Both
grow logistically with a shared carrying capacity $K$, infection follows a ratio-dependent
(frequency-dependent) law, and the virus kills infected cells at rate $a$:

$$\dot X = r_1 X\Bigl(1 - \frac{X + Y}{K}\Bigr) - \frac{b X Y}{X + Y}, \qquad
\dot Y = r_2 Y\Bigl(1 - \frac{X + Y}{K}\Bigr) + \frac{b X Y}{X + Y} - a Y,$$

with $r_1, r_2, b, a, K > 0$ and $X(0), Y(0) > 0$. With $x = X/K$, $y = Y/K$, $\tau = r_1 t$ and
$\beta = b/r_1$, $\gamma = r_2/r_1$, $\delta = a/r_1$:

$$x' = x(1 - x - y) - \frac{\beta x y}{x + y}, \qquad
y' = \gamma y(1 - x - y) + \frac{\beta x y}{x + y} - \delta y .$$

**Results.**

1. The triangle $\Omega = \{ x, y \ge 0,\ x + y \le 1 \}$ is positively invariant and every
   trajectory in the positive quadrant enters it in finite time.
2. There are no closed orbits: $D(x, y) = 1/(xy)$ is a Dulac function.
3. Equilibria: the origin $O$ (not analytic, so linearization fails); $A_1 = (1, 0)$, a stable node
   if $\delta > \beta$ and a saddle if $\delta < \beta$; $A_2 = (0, (\gamma - \delta)/\gamma)$, in
   $\Omega$ iff $\gamma > \delta$, a stable node if $\delta < \beta\gamma$ and a saddle if
   $\delta > \beta\gamma$; and

    $$A_3 = \bigl(k(\beta\gamma - \delta),\ k(\delta - \beta)\bigr), \qquad
    k = \frac{\beta - 1 + \gamma - \delta}{\beta(\gamma - 1)^2}.$$

4. When $A_3 \in \Omega$ it is an asymptotically stable node if $\beta > \delta$ and a saddle if
   $\beta < \delta$; in the first case it is globally asymptotically stable in the open positive
   quadrant. Positivity of $A_3$ amounts to $\delta < \beta$, $\beta\gamma < \delta$,
   $\beta + \gamma < 1 + \delta$ (node case) or $\beta < \delta < \beta\gamma$,
   $\beta + \gamma > 1 + \delta$ (saddle case).

## Expansion

The two boundary equilibria are read off directly: near $A_1$ the infected equation linearizes to
$y' \approx (\beta - \delta) y$, so infection invades a virus-free tumour exactly when the scaled
infection rate exceeds the scaled cytotoxicity; near $A_2$ the uninfected equation is
$x' \approx x(\delta/\gamma - \beta)$. Since there are no cycles and $\Omega$ is absorbing, the
Poincaré–Bendixson theorem reduces the global dynamics to the equilibria and their separatrices. The
new feature, absent from the mass-action version of the model, is the singular origin: after the
time change $d\tau \to (x + y)\, d\tau$ its neighbourhood can contain hyperbolic, parabolic and
elliptic sectors, and for suitable $(\beta, \gamma, \delta)$ the origin has an open basin of
attraction. Trajectories in it converge to $(0, 0)$, which is complete elimination of the tumour by
the virus in finite or infinite time, a regime the mass-action model cannot produce.

## Sources

- A. S. Novozhilov, F. S. Berezovskaya, E. V. Koonin, G. P. Karev, "Mathematical modeling of tumor
  therapy with oncolytic viruses: regimes with complete tumor elimination within the framework of
  deterministic models", Biology Direct 1 (2006) 6, model (4), rescaled system (10), Lemmas 1-3 and
  Propositions 1-4, <https://doi.org/10.1186/1745-6150-1-6> (PMC1403749).
