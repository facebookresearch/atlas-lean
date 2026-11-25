# Lyapunov–Schmidt reduction to a scalar equation near a zero of F

Let $E$, $Y$ and $\Lambda$ be real Banach spaces, let $L : E \to Y$ be a bounded linear map, and fix
a Fredholm package of $L$: decompositions $E = X_1 \oplus X_0$ and $Y = Y_1 \oplus Y_0$ into
topologically complementary subspaces with $X_0$ and $Y_0$ finite-dimensional, and an isomorphism
$A : X_1 \to Y_1$ of normed spaces, such that $L x = A(\pi_1 x)$ for every $x$, where $\pi_1$ is the
projection onto $X_1$ along $X_0$. Then $\ker L = X_0$ and $\operatorname{range} L = Y_1$. Write $Q$
for the projection of $Y$ onto $Y_1$ along $Y_0$ and $\pi_0$ for the projection of $E$ onto $X_0$
along $X_1$. Let $F : E \times \Lambda \to Y$ be strictly differentiable at $(0, p_0)$ with
derivative $F'$ whose restriction to $E$ is $L$: $F'(x, 0) = L x$, so $L$ is the state derivative
$\partial_x F(0, p_0)$. Assume $F(0, p_0) = 0$. Let $\varphi \in X_0$ and let
$\psi : Y \to \mathbb{R}$ be a bounded linear functional, with the
[scalar bifurcation function](ls-scalar.md)
$\tilde G(a, p) = \psi(F(a\varphi + W(a\varphi, p), p))$, where $W$ is the
[solution operator](ls-solution.md). Assume every $z \in X_0$ is a real multiple of $\varphi$, and
that $\psi$ vanishes on $Y_1 = \operatorname{range} L$ and is injective on $Y_0$.

Then for $(x, p)$ near $(0, p_0)$, $F(x, p) = 0$ if and only if there is $a \in \mathbb{R}$ with

$$x = a\varphi + W(a\varphi, p) \quad \text{and} \quad \tilde G(a, p) = 0.$$

The kernel has dimension at most one and $\operatorname{range} L$ codimension at most one;
$\varphi = 0$ and $\psi = 0$ are allowed, so the index of $L$ need not be zero.
