# Quadratic binary mean-field free energy

Let $d \ge 1$, let $U$ be a real symmetric $d \times d$ matrix with operator norm
$\|U\| \le a < 1$ for the Euclidean norm, and let $h \in \mathbb{R}^d$. For $t \in [-1, 1]$ let

$$H(t) = -\frac{1 + t}{2} \log \frac{1 + t}{2} - \frac{1 - t}{2} \log \frac{1 - t}{2},$$

with $0 \log 0 = 0$, be the entropy of a $\pm 1$ variable with mean $t$; it is continuous on
$[-1, 1]$ and $H(\pm 1) = 0$. On the closed cube $[-1, 1]^d$ define

$$F(m) = -\sum_{i=1}^{d} H(m_i) - \tfrac{1}{2} \langle m, U m \rangle - \langle h, m \rangle .$$

Then:

- (a) On the open cube $(-1, 1)^d$, $F$ is smooth and
  $\nabla F(m) = \operatorname{artanh}(m) - U m - h$, with $\operatorname{artanh}$ applied
  coordinatewise.
- (b) On the open cube, $\nabla^2 F(m) = \operatorname{diag}\bigl((1 - m_i^2)^{-1}\bigr) - U
  \succeq (1 - a) I$, so $F$ is strongly convex there.
- (c) $F$ has exactly one critical point in the open cube. It is the unique fixed point $m^\star$
  of $m \mapsto \tanh(U m + h)$ and the unique minimizer of $F$ over the open cube.

Proof: (a) For $t \in (-1, 1)$, $H'(t) = -\tfrac{1}{2} \log \frac{1 + t}{1 - t} =
-\operatorname{artanh}(t)$. The gradient of $\tfrac{1}{2} \langle m, U m \rangle$ is
$\tfrac{1}{2} (U + U^{\mathsf{T}}) m = U m$ because $U$ is symmetric; without symmetry the
gradient equation would involve $\tfrac{1}{2} (U + U^{\mathsf{T}})$ instead. (b)
$\operatorname{artanh}'(t) = (1 - t^2)^{-1} \ge 1$ on $(-1, 1)$, and $U \preceq \|U\| I \preceq a I$
because $U$ is symmetric, so $\nabla^2 F(m) \succeq I - a I$. (c) By (a), $m$ in the open cube is a
critical point exactly when $\operatorname{artanh}(m) = U m + h$, which holds exactly when $m$ is a
fixed point of $T(m) = \tanh(U m + h)$. Since $\tanh$ is $1$-Lipschitz and $\|U\| \le a < 1$, $T$ is
a contraction of $\mathbb{R}^d$ with constant $a$. Banach's fixed-point theorem on the complete
space $\mathbb{R}^d$ gives a unique fixed point, and it lies in the open cube because every value of
$\tanh$ does; equivalently, $T$ maps the complete closed cube into its interior, so it is a
contraction of the closed cube with the same fixed point. A strongly convex function on the convex
open cube attains its minimum over the cube at any critical point, and only there. No coercivity of
$F$ is used: $F$ stays bounded near the boundary of the cube; only its gradient diverges.

This page does not claim that $m^\star$ minimizes $F$ over the closed cube; that would need a
separate argument.

**Ising product law (derived).** Let $A$ be a real symmetric $d \times d$ matrix, let
$p(\sigma) \propto \exp\bigl(\tfrac{1}{2} \sigma^{\mathsf{T}} A \sigma + h^{\mathsf{T}} \sigma\bigr)$ on
$\{-1, 1\}^d$, and let $q$ be a product law on $\{-1, 1\}^d$ with means $m_i$. Under $q$,
$\mathbb{E}[\sigma_i \sigma_j] = m_i m_j$ for $i \ne j$ but $\mathbb{E}[\sigma_i^2] = 1$. Hence
$\mathbb{E}_q\bigl[\tfrac{1}{2} \sigma^{\mathsf{T}} A \sigma\bigr] = \tfrac{1}{2} m^{\mathsf{T}} A m
+ \tfrac{1}{2} \sum_i A_{ii} (1 - m_i^2)$, and the evidence lower bound of $q$ against the
unnormalized weights satisfies

$$-\mathrm{ELBO}(q) = F_A(m) - \tfrac{1}{2} \sum_{i=1}^{d} A_{ii} (1 - m_i^2)
= F_{A - \operatorname{diag}(A)}(m) - \tfrac{1}{2} \sum_{i=1}^{d} A_{ii},$$

where $F_U$ denotes $F$ with coupling $U$. So the product-law stationarity equation is
$\operatorname{artanh}(m) = (A - \operatorname{diag}(A)) m + h$, and (c) applies when
$\|A - \operatorname{diag}(A)\| \le a < 1$. The diagonal correction belongs to this link only; the
statements (a)–(c) hold for any symmetric $U$ with $\|U\| \le a < 1$, whatever its diagonal. The
two-factor coordinate ascent on this page's topic is a different setting and is not used here.

## Informally uses

- [Fixed points of the mean-field map are the solutions of artanh m = U m + h](mean-field-map-eq-self-iff.md):
  mathematical prerequisite, the equivalence of the critical-point equation in (c) with the
  fixed-point equation, for $U$ viewed as a linear map on $\mathbb{R}^d$ with the Euclidean norm.
- [Existence and uniqueness of the mean-field fixed point](exists-unique-mean-field-map-eq-self.md):
  mathematical prerequisite, the unique fixed point in (c).
- [The mean-field map is a contraction for a coupling of norm below one](contracting-with-mean-field-map.md):
  mathematical prerequisite, the contraction in (c).

## Background

- [Error of an approximate mean-field iteration](dist-iterate-le-of-dist-le-mean-field-ma.md):
  background, how far iterates of an approximation of $T$ stay from $m^\star$.

## Sources

- S. Mei and Y. Wu, "Deep networks as denoising algorithms: sample-efficient learning of diffusion models in high-dimensional graphical models", arXiv:2309.11420 (version 1), page 29 (the quadratic free energy with coupling $U = A - K$, which must itself be symmetric, and its Hessian, displayed there without the inverse on the diagonal term; page 33 has the inverse) and equation (40) on page 29 (the approximate-iteration error recursion).
- AI-authored exposition.
