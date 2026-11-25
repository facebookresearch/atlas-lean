# Lyapunov–Schmidt solution operator W

Let $E$, $Y$ and $\Lambda$ be real Banach spaces, let $L : E \to Y$ be a bounded linear map, and fix
a Fredholm package of $L$: decompositions $E = X_1 \oplus X_0$ and $Y = Y_1 \oplus Y_0$ into
topologically complementary subspaces with $X_0$ and $Y_0$ finite-dimensional, and an isomorphism
$A : X_1 \to Y_1$ of normed spaces, such that $L x = A(\pi_1 x)$ for every $x$, where $\pi_1$ is the
projection onto $X_1$ along $X_0$. Then $\ker L = X_0$ and $\operatorname{range} L = Y_1$. Write $Q$
for the projection of $Y$ onto $Y_1$ along $Y_0$ and $\pi_0$ for the projection of $E$ onto $X_0$
along $X_1$. Let $F : E \times \Lambda \to Y$ be strictly differentiable at $(0, p_0)$ with
derivative $F'$ whose restriction to $E$ is $L$: $F'(x, 0) = L x$, so $L$ is the state derivative
$\partial_x F(0, p_0)$.

The solution operator $W : X_0 \times \Lambda \to X_1$ is the implicit function, given by the
implicit function theorem, of the [range equation](ls-range-map.md) through $((0, p_0), 0)$: for
$(z, p)$ near $(0, p_0)$, $Q\, F(z + W(z, p), p) = Q\, F(0, p_0)$. It is defined on all of
$X_0 \times \Lambda$, but only its values near $(0, p_0)$ are meaningful. When $F(0, p_0) = 0$, near
$((0, p_0), 0)$ the range equation $Q\, F(z + w, p) = 0$ holds exactly when $w = W(z, p)$.
