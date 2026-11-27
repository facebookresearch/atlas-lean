# Uniqueness for the Dirichlet problem for Poisson's equation

Let $U$ be a bounded open subset of a nontrivial finite-dimensional real inner product space and
let $f : U \to \mathbb{R}$ be any function. If $u_1, u_2 \in C^2(U) \cap C(\overline U)$ both solve

$$-\Delta u = f \text{ in } U, \qquad u = g \text{ on } \partial U$$

for the same boundary values $g$, then $u_1 = u_2$ on $\overline U$. No regularity of $f$ or $g$ is
needed. In dimension $0$
uniqueness fails, which is why the space is assumed nontrivial.

## Informally uses

- [Weak maximum principle for harmonic functions](exists-mem-frontier-is-max-on-of-harmoni.md) and
  [weak minimum principle](exists-mem-frontier-is-min-on-of-harmoni.md): applied to the harmonic
  function $u_1 - u_2$, which vanishes on $\partial U$.

## Sources

- L. C. Evans, *Partial Differential Equations*, 2nd ed., AMS Graduate Studies in Mathematics 19 (2010), Chapter 2. Not consulted directly; no theorem number is cited from it.
- M. Schmidt, *Partial Differential Equations*, lecture notes, Universität Mannheim, HWS 2025, [Chapter 3 (Laplace equation)](https://www.wim.uni-mannheim.de/media/Lehrstuehle/wim/schmidt/HWS2025/chapter_3.pdf), §3.3.
