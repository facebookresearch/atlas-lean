# Pattern branch of F(x, d) = 0 from the reduced branch theorem

Let $E$ and $Y$ be real Banach spaces, let $L : E \to Y$ be a bounded linear map, and fix a Fredholm
package of $L$: decompositions $E = X_1 \oplus X_0$ and $Y = Y_1 \oplus Y_0$ into topologically
complementary subspaces with $X_0$ and $Y_0$ finite-dimensional, and an isomorphism
$A : X_1 \to Y_1$ of normed spaces, such that $L x = A(\pi_1 x)$ for every $x$, where $\pi_1$ is the
projection onto $X_1$ along $X_0$. Then $\ker L = X_0$ and $\operatorname{range} L = Y_1$. Write $Q$
for the projection of $Y$ onto $Y_1$ along $Y_0$ and $\pi_0$ for the projection of $E$ onto $X_0$
along $X_1$. Let $F : E \times \mathbb{R} \to Y$ be strictly differentiable at $(0, d_0)$ with
derivative $F'$, $F'(x, 0) = L x$, with the trivial branch $F(0, d) = 0$ for $d$ near $d_0$. Let
$\varphi \in X_0$ be nonzero with every $z \in X_0$ a real multiple of $\varphi$, and let
$\psi : Y \to \mathbb{R}$ be a bounded linear functional that vanishes on
$Y_1 = \operatorname{range} L$ and is injective on $Y_0$. Let $W$ be the
[solution operator](ls-solution.md) and $\tilde G(a, d) = \psi(F(a\varphi + W(a\varphi, d), d))$ the
[scalar bifurcation function](ls-scalar.md). Assume:

- **factorization:** $\tilde G(a, d) = a\, G(a, d)$ for $(a, d)$ near $(0, d_0)$, where
  $G : \mathbb{R} \times \mathbb{R} \to \mathbb{R}$ is strictly differentiable at $(0, d_0)$ with
  derivative $G'$, $G(0, d_0) = 0$ and $\partial_d G(0, d_0) = G'(0, 1) \neq 0$;
- **reduced branch theorem for $G$:** under these conditions on $G$ there is
  $\beta : \mathbb{R} \to \mathbb{R}$ with $\beta(0) = d_0$, strictly differentiable at $0$ with
  derivative $-G'(1, 0)/G'(0, 1)$, such that near $(0, d_0)$, $a\, G(a, d) = 0$ if and only if
  $a = 0$ or $d = \beta(a)$. This holds for every such $G$
  ([zeros of $a\, G(a, d)$](../bifurcation-of-turing-pattern-branches/exists-pattern-branch.md)) and
  enters here as a hypothesis.

Then there is $\beta : \mathbb{R} \to \mathbb{R}$ with $\beta(0) = d_0$, strictly differentiable at
$0$ with derivative $-G'(1, 0)/G'(0, 1)$, such that:

- for $(x, d)$ near $(0, d_0)$, $F(x, d) = 0$ if and only if $x = 0$, or
  $x = a\varphi + W(a\varphi, d)$ and $d = \beta(a)$ for some $a \in \mathbb{R}$;
- for every $a$ near $0$, $F(a\varphi + W(a\varphi, \beta(a)), \beta(a)) = 0$.
