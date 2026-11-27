# Non-abelian 1-cochains and unique-games coboundary expansion

Let $X$ be a pure weighted complex of dimension at least $2$ and $\Gamma$ a (possibly non-abelian) group. A **$\Gamma$-valued $1$-cochain** is a function $f$ on oriented edges with $f(v, u) = f(u, v)^{-1}$. Its coboundary on a triangle $\{u, v, w\}$ is the triangle holonomy $(\delta f)(u, v, w) = f(u,v)\, f(v,w)\, f(w,u)$, and $f$ is a **cocycle** if $\delta f \equiv 1$. The coboundaries are the cochains $(\delta h)(u, v) = h(u)\, h(v)^{-1}$ for $h : X(0) \to \Gamma$.

$X$ has **$\beta$-coboundary expansion over $\Gamma$** in dimension $1$ if for every $f$,

$$
\Pr_{\{u,v,w\} \sim \Pi_2}\bigl[(\delta f)(u,v,w) \ne 1\bigr] \ge \beta \cdot \min_{h} \Pr_{\{u,v\} \sim \Pi_1}\bigl[f(u,v) \ne h(u)h(v)^{-1}\bigr].
$$

In Bafna–Minzer's higher-level formulation on the $t$-face graphs $G_t[X]$ (with edges $E_t[X]$ sampled from $\mu_{2t}$ and triangles from $\mu_{3t}$), a $d$-dimensional simplicial complex $X$ is an **$(m, r, \xi, c)$ unique-games (UG) coboundary expander** (Definition 1.4) if for every $t \le r$ and every $(1-\xi)$-triangle-consistent function $\pi \colon E_t[X] \to S_m$, there exists $g \colon X(t) \to S_m$ such that $\Pr_{u \cup v \sim \mu_{2t}}[\pi(u,v) = g(u)g(v)^{-1}] \ge 1 - c$ (Remark 1.6 notes that the edge-level $\beta$-coboundary definition above coincides with this only at $t = 1$). It is a **weak $(m, r, \xi, c)$ UG coboundary expander** (Definitions 1.7–1.8) if the same conclusion holds for every $(1-\xi)$-*strongly* triangle-consistent $\pi \colon E_t[X] \to S_m$, meaning there exist lists $L \colon X(t) \to (\{0,1\}^t)^m$ and $L' \colon X(3t) \to (\{0,1\}^{3t})^m$ such that $\Pr_{T=u\cup v\cup w \sim \mu_{3t}}[L'(T) = L(u)\circ \pi(u,v)L(v)\circ \pi(u,w)L(w)] \ge 1 - \xi$. Bafna and Minzer note that non-weak UG coboundary expansion may not be necessary for low-soundness direct product testing, whereas weak UG coboundary expansion is both necessary and sufficient.

## Depends on

- [Coboundary expansion of a simplicial complex](coboundary-expansion.md)

## Sources

- M. Bafna, D. Minzer, "Characterizing direct product testing via coboundary expansion", STOC (2024), arXiv:2308.09668.
- Y. Dikstein, I. Dinur, "Agreement theorems for high dimensional expanders in the small soundness regime: the role of covers", arXiv:2308.09582 (2023), ECCC TR23-119.
- Y. Dikstein, I. Dinur, "Coboundary and cosystolic expansion without dependence on dimension or degree", APPROX-RANDOM (2023), ECCC TR23-043.
