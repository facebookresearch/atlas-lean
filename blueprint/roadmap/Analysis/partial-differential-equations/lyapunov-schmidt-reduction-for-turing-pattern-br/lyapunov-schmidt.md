# Lyapunov–Schmidt reduction near a zero of F

Let $E$, $Y$ and $\Lambda$ be real Banach spaces, let $L : E \to Y$ be a bounded linear map, and fix
a Fredholm package of $L$: decompositions $E = X_1 \oplus X_0$ and $Y = Y_1 \oplus Y_0$ into
topologically complementary subspaces with $X_0$ and $Y_0$ finite-dimensional, and an isomorphism
$A : X_1 \to Y_1$ of normed spaces, such that $L x = A(\pi_1 x)$ for every $x$, where $\pi_1$ is the
projection onto $X_1$ along $X_0$. Then $\ker L = X_0$ and $\operatorname{range} L = Y_1$. Write $Q$
for the projection of $Y$ onto $Y_1$ along $Y_0$ and $\pi_0$ for the projection of $E$ onto $X_0$
along $X_1$. Let $F : E \times \Lambda \to Y$ be strictly differentiable at $(0, p_0)$ with
derivative $F'$ whose restriction to $E$ is $L$: $F'(x, 0) = L x$, so $L$ is the state derivative
$\partial_x F(0, p_0)$. Assume $F(0, p_0) = 0$.

Then for $(x, p)$ near $(0, p_0)$, $F(x, p) = 0$ if and only if

$$\pi_1 x = W(\pi_0 x, p) \quad \text{and} \quad g(\pi_0 x, p) = 0,$$

where $\pi_1 x$ is the essential component of $x$, $W$ the [solution operator](ls-solution.md) and
$g$ the [reduced map](ls-reduced.md) $g(z, p) = (1 - Q)\, F(z + W(z, p), p) \in Y_0$: near
$(0, p_0)$ the zeros of $F$ correspond to the zeros of the bifurcation equation on the
finite-dimensional kernel $X_0$.
