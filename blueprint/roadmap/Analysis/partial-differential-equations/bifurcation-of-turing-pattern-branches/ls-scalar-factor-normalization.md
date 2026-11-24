# A factor G of the reduced map has G(0, d₀) = 0, ∂_d G(0, d₀) = ψ(L₁φ)

Let $E$ and $Y$ be real Banach spaces, let $L : E \to Y$ be a bounded linear map, and fix a Fredholm
package of $L$: decompositions $E = X_1 \oplus X_0$ and $Y = Y_1 \oplus Y_0$ into topologically
complementary subspaces with $X_0$ and $Y_0$ finite-dimensional, and an isomorphism $X_1 \to Y_1$
through which $L$ factors, so that $\ker L = X_0$ and $\operatorname{range} L = Y_1$. Let
$F : E \times \mathbb{R} \to Y$ be strictly differentiable at $(0, d_0)$ with derivative $F'$,
$F'(x, 0) = L x$, with the trivial branch $F(0, d) = 0$ for $d$ near $d_0$. Let $\varphi \in X_0$,
and let $\psi : Y \to \mathbb{R}$ be a bounded linear functional that vanishes on
$Y_1 = \operatorname{range} L$, with
[scalar bifurcation function](../lyapunov-schmidt-reduction-for-turing-pattern-br/ls-scalar.md)
$\tilde G(a, d) = \psi(F(a\varphi + W(a\varphi, d), d))$ for the
[solution operator](../lyapunov-schmidt-reduction-for-turing-pattern-br/ls-solution.md) $W$. Assume:

- **affine linearization:** for a bounded linear $L_1 : E \to Y$ and every $d$ near $d_0$, the map
  $x \mapsto F(x, d)$ is differentiable at $0$ with derivative $L + (d - d_0) L_1$;
- **factorization:** $\tilde G(a, d) = a\, G(a, d)$ for $(a, d)$ near $(0, d_0)$, with
  $G : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ strictly differentiable at $(0, d_0)$ with
  derivative $G'$.

Then $G(0, d_0) = 0$ and $\partial_d G(0, d_0) = G'(0, 1) = \psi(L_1 \varphi)$. Nothing is assumed
about $G(0, d)$ for $d \neq d_0$, and $G$ need not be continuous away from $(0, d_0)$. For
$\psi(L_1\varphi) \neq 0$ these are the conditions on $G$ of the
[pattern branch theorem](../lyapunov-schmidt-reduction-for-turing-pattern-br/lyapunov-schmidt-pattern-branch.md).
