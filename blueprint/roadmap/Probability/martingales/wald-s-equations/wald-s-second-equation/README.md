# Wald's second equation

Let $(\Omega, \mathbb{P})$ be a probability space with a filtration $(\mathcal{F}_k)_{k \ge 0}$, and let
$X_0, X_1, \dots$ be identically distributed real random variables with $\mathbb{E}|X_0| < \infty$,
$\mathbb{E}[X_0] = 0$ and $\mathbb{E}[X_0^2] < \infty$. Let $T$ be an $\mathbb{N}$-valued stopping time for
$(\mathcal{F}_k)$ with $\mathbb{E}[T] < \infty$, and suppose that each $X_k$ is independent of
$\mathcal{F}_k$ and $\mathcal{F}_{k+1}$-measurable. Then
$\mathbb{E}\big[\big(\sum_{i < T} X_i\big)^2\big] = \mathbb{E}[X_0^2] \cdot \mathbb{E}[T]$.

## Idea

For centred steps, the stopped sum has second moment $\mathbb{E}[X_0^2]\, \mathbb{E}[T]$, as if the number
of steps were fixed. Expanding the square of $S_T = \sum_k X_k \mathbf{1}_{\{T > k\}}$, the diagonal
part $\sum_k X_k^2 \mathbf{1}_{\{T > k\}}$ has mean $\mathbb{E}[X_0^2]\, \mathbb{E}[T]$ by Wald's equation
applied to the squares. A cross term $X_j X_k \mathbf{1}_{\{T > k\}}$ with $j < k$ has mean zero, because
$X_j$ and the event $\{T > k\}$ are $\mathcal{F}_k$-measurable while $X_k$ is independent of
$\mathcal{F}_k$ with mean zero; adding up infinitely many cross terms needs care, done first for bounded
stopping times. Consequences are that the stopped sum is square integrable and, with Doob's maximal
inequality, so is its running maximum up to $T$.

## Statements

- [Wald's second equation](wald-second-equation.md)
- [Diagonal identity in Wald's second equation](wald-diagonal-terms.md): diagonal part of the classical expansion proof of the second equation
- [Vanishing of the cross terms in Wald's second equation](wald-cross-terms-zero.md): cross-term part of that expansion proof, under a summability hypothesis
- [Cross terms vanish for a bounded stopping time](wald-cross-terms-zero-of-bounded.md): cross terms of that expansion for bounded stopping times
- [Vanishing of a single cross term in Wald's second equation](cross-pair-integral-zero.md): a single cross term of that expansion; lemma for the two cross-term statements
- [Square of a finite sum as diagonal plus cross terms](sum-sq-expansion.md): algebraic identity behind the split into diagonal and cross terms
- [Integrability of the stopped sum of squares](integrable-stopped-sum-sq-diag.md): integrability of the diagonal part
- [Square-integrability of a stopped partial sum](integrable-stopped-partial-sum-sq.md): consequence of the second equation: the stopped sum is square-integrable
- [Square-integrability of the maximal stopped partial sum](integrable-maximal-stopped-partial-sum-s.md): square-integrability of the running maximum up to $T$, proved with the second equation
- [Predictable filtration of a sequence](predictable-filtration.md): definition of the filtration used by the running-maximum statement
- [Predictable filtration at time zero is trivial](predictable-filtration-zero.md): basic property of the predictable filtration
- [Successor step of the predictable filtration](predictable-filtration-succ.md): basic property of the predictable filtration

## Background

- [Wald's equation](../wald-s-equation/README.md): Wald's equation, applied to the squares for the diagonal part
- [Doob's $L^2$ maximal inequality](../../doob-s-maximal-inequalities/README.md): the maximal inequality used for the running maximum
