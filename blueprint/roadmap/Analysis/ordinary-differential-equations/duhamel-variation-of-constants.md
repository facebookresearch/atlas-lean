# Duhamel's formula (variation of constants)

Let $E$ be a real Banach space, let
$A : E \to E$ be a bounded linear operator, let $b : \mathbb{R} \to E$ be continuous, and let
$t_0 \in \mathbb{R}$ and $x_0 \in E$. Write $e^{sA}$ for the operator exponential and define
$x : \mathbb{R} \to E$ by
$x(t) = e^{(t - t_0)A} x_0 + \int_{t_0}^{t} e^{(t - s)A} b(s)\, ds$.
Then $x(t_0) = x_0$ and $x$ is differentiable with $x'(t) = A x(t) + b(t)$ for every
$t \in \mathbb{R}$. Moreover $x$ is the only such solution: every $y : \mathbb{R} \to E$ with
$y(t_0) = x_0$ and $y'(t) = A y(t) + b(t)$ for every $t \in \mathbb{R}$ equals $x$.

Proof: Factor the propagator by the commuting exponential group law, differentiate the
integrating-factor primitive, and apply global Lipschitz uniqueness. This follows Teschl,
Sections 3.2 and 3.4, formula (3.48) and Theorem 3.12 / (3.97).

## Sources

- G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 3.2; stable ref https://en.wikipedia.org/wiki/Duhamel%27s_principle.
