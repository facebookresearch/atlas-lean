# A line of fast diffusion speeds up epidemic spreading exactly when D > 2d

**Model (SIRT).** In the upper half-plane $\{(x, y) : x \in \mathbb{R}, y > 0\}$ ("the field"), infected individuals $I$ diffuse with diffusivity $d > 0$ and susceptibles $S$ do not move, as in the [spatial SIR model](spreading-speed-of-the-spatial-sir-model.md). On the boundary line $\{y = 0\}$ ("the road") a population of travelling infected individuals $T(t, x)$ diffuses with diffusivity $D > 0$ and exchanges with the field at rates $\nu, \mu > 0$:

$$\begin{aligned}
&\partial_t I - d\,\Delta I + \alpha I = \beta S I, \qquad \partial_t S = -\beta S I, && y > 0,\\
&-d\, \partial_y I(t, x, 0) = \mu T - \nu I(t, x, 0), \qquad \partial_t T - D\, \partial_{xx} T = \nu I(t, x, 0) - \mu T, && y = 0,
\end{aligned}$$

with $S(0, \cdot) \equiv S_0 > 0$ and nonnegative compactly supported initial infections $I_0 \not\equiv 0$, $T_0$. With $u = \int_0^t T\, ds$, $v = \int_0^t I\, ds$ and $f(v) = S_0(1 - e^{-\beta v}) - \alpha v$, the system becomes

$$\partial_t u - D\, \partial_{xx} u = \nu v(t, x, 0) - \mu u + T_0, \quad \partial_t v - d\, \Delta v = f(v) + I_0, \quad -d\, \partial_y v(t, x, 0) = \mu u - \nu v(t, x, 0).$$

**Theorem (Berestycki, Roquejoffre and Rossi 2020, Theorems 3.4–3.6).** The reduced system has a unique positive bounded stationary solution $(u_\infty^r, v_\infty^r)$, and $(u, v) \to (u_\infty^r, v_\infty^r)$ locally uniformly as $t \to \infty$. If $R_0 = S_0 \beta / \alpha > 1$, there is $c_{\mathrm{SIRT}} > 0$ such that for every $\varepsilon \in (0, c_{\mathrm{SIRT}})$,

$$\lim_{t \to \infty} \max_{|x| \le (c_{\mathrm{SIRT}} - \varepsilon) t} \big| (u, v)(t, x, y) - (u_\infty^r, v_\infty^r)(x, y) \big| = 0, \qquad \lim_{t \to \infty} \max_{|x| \ge (c_{\mathrm{SIRT}} + \varepsilon) t} |(u, v)(t, x, y)| = 0,$$

locally uniformly in $y \ge 0$, and

$$c_{\mathrm{SIRT}} = c_{\mathrm{SIR}} = 2\sqrt{d\, \alpha (R_0 - 1)} \ \text{ if } D \le 2d, \qquad c_{\mathrm{SIRT}} > c_{\mathrm{SIR}} \ \text{ if } D > 2d.$$

## Depends on

- [Spreading speed of the spatial SIR model with immobile susceptibles](spreading-speed-of-the-spatial-sir-model.md)

## Expansion

The integrated system is the field–road KPP system of Berestycki, Roquejoffre and Rossi (2013) with compactly supported source terms. A compactly supported source cannot slow propagation (comparison principle) and does not change the far-field linearization, so the spreading speed equals that of the source-free road–field system. For that system, exponential supersolutions $e^{-a(x - ct)}$ on the road coupled to field profiles show that the speed along the road is the KPP speed $2\sqrt{d f'(0)}$ when $D \le 2d$, and strictly larger when $D > 2d$: fast transport on the road seeds infection ahead of the field front, which then spreads back into the field.

## Sources

- H. Berestycki, J.-M. Roquejoffre and L. Rossi, "Propagation of Epidemics Along Lines with Fast Diffusion", Bulletin of Mathematical Biology 83 (2021), 2, Section 3.2 (system (7)–(8), Theorems 3.4–3.6), <https://doi.org/10.1007/s11538-020-00826-8> (PMC7734393).
