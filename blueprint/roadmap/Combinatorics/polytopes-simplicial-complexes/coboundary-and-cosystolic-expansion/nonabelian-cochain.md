# Non-abelian 1-cochains and unique-games coboundary expansion

Let $X$ be a pure weighted complex of dimension at least $2$ and $\Gamma$ a (possibly non-abelian) group. A **$\Gamma$-valued $1$-cochain** is a function $f$ on oriented edges with $f(v, u) = f(u, v)^{-1}$. Its coboundary on a triangle $\{u, v, w\}$ is the triangle holonomy $(\delta f)(u, v, w) = f(u,v)\, f(v,w)\, f(w,u)$, and $f$ is a **cocycle** if $\delta f \equiv 1$. The coboundaries are the cochains $(\delta h)(u, v) = h(u)\, h(v)^{-1}$ for $h : X(0) \to \Gamma$.

$X$ has **$\beta$-coboundary expansion over $\Gamma$** in dimension $1$ if for every $f$,

$$
\Pr_{\{u,v,w\} \sim \Pi_2}\bigl[(\delta f)(u,v,w) \ne 1\bigr] \ge \beta \cdot \min_{h} \Pr_{\{u,v\} \sim \Pi_1}\bigl[f(u,v) \ne h(u)h(v)^{-1}\bigr].
$$

**Unique-games coboundary expansion** (Bafna–Minzer, Definition 1.4) asks for this simultaneously for all symmetric groups $\Gamma = S_m$, $m \ge 1$, with $\beta$ independent of $m$. **Weak unique-games coboundary expansion** (Bafna–Minzer, Definition 1.8) relaxes the requirement to cochains that are $(1-\xi)$-*strongly* triangle-consistent (rather than arbitrary $1$-cochains), asking for an approximate global trivialization; Bafna and Minzer note that ordinary (non-weak) UG coboundary expansion may not be necessary for low-soundness direct product testing, whereas the weak condition on the $t$-face graphs $G_t[X]$ is both necessary and sufficient.

## Depends on

- [Coboundary expansion of a simplicial complex](coboundary-expansion.md)

## Sources

- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668.
- Y. Dikstein, I. Dinur, "Agreement theorems for high dimensional expanders in the small soundness regime: the role of covers", arXiv:2308.09582 (2023), ECCC TR23-119.
- Y. Dikstein, I. Dinur, "Coboundary and cosystolic expansion without dependence on dimension or degree", APPROX-RANDOM (2023), ECCC TR23-043.
