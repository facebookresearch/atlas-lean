# Brenier's theorem

Let $\mu$ and $\nu$ be probability measures on $\mathbb{R}^n$ with finite second moments, and assume
that $\mu$ is absolutely continuous with respect to Lebesgue measure. For the quadratic cost
$c(x, y) = |x - y|^2$ there is a measurable map $T : \mathbb{R}^n \to \mathbb{R}^n$ such that

- the coupling $\pi_T = (\mathrm{id}, T)_\# \mu$ is a coupling of $\mu$ and $\nu$ and is optimal:
  $\int |x - y|^2 \, d\pi_T = \inf_\pi \int |x - y|^2 \, d\pi$;
- every optimal coupling of $\mu$ and $\nu$ equals $\pi_T$;
- $T$ is $\mu$-almost everywhere the gradient of a convex function: there are an open convex set
  $U$ with $\mu(\mathbb{R}^n \setminus U) = 0$ and a function $\psi$ convex on $U$ with
  $\nabla \psi(x) = T(x)$ for $\mu$-almost every $x$.

Villani's Theorem 9.4 assumes only that $\mu$ does not give mass to sets of dimension at most $n - 1$,
which holds in particular when $\mu$ is absolutely continuous; the statement here is that case. There
the optimal coupling is characterised by $y \in \partial \psi(x)$ almost surely for a lower
semicontinuous convex $\psi : \mathbb{R}^n \to \mathbb{R} \cup \{+\infty\}$. When $\mu$ is absolutely
continuous, $\mu$-almost every $x$ lies in the interior $U$ of the domain of $\psi$, where $\psi$ is
finite, convex and differentiable almost everywhere with $\partial \psi(x) = \{\nabla \psi(x)\}$; this
gives the gradient form above.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Theorem 9.4 (Monge problem for quadratic cost, first result).
