# Existence and uniqueness of the JKO step

Let $\Psi : \mathbb{R}^n \to \mathbb{R}$ be $C^\infty$ with $\Psi \ge 0$ and
$|\nabla \Psi(x)| \le C (\Psi(x) + 1)$ for some constant $C$, and let $\beta > 0$ and $h > 0$. For
every [admissible](is-admissible.md) $\rho_0$ there is exactly one [JKO step](is-jkostep.md) from
$\rho_0$: a unique admissible minimizer of $\tfrac12 W_2(\rho_0, \rho)^2 + h F(\rho)$, where
$F(\rho) = \int \Psi \rho + \beta^{-1} \int \rho \log \rho$.

The assumptions on $\Psi$ allow $\int e^{-\beta \Psi} = \infty$, so the heat equation
($\Psi$ constant) is included. In the paper, uniqueness follows from the convexity of $K$
and the strict convexity of the objective under linear interpolation of densities: $S$ is strictly
convex, $E$ is linear and $\rho \mapsto W_2(\rho_0, \rho)^2$ is convex. The statement is posed on any finite-dimensional real inner product
space with its Lebesgue measure.

## Background

- [Existence of a JKO step on a proper metric space](exists-is-minimizing-movement-step.md): the
  compactness argument that works when closed balls are compact, which is not the case here.

## Sources

- R. Jordan, D. Kinderlehrer, F. Otto, *The variational formulation of the Fokker–Planck equation*, SIAM J. Math. Anal. 29 (1998), 1–17, Proposition 4.1, under the assumptions of Section 4.
