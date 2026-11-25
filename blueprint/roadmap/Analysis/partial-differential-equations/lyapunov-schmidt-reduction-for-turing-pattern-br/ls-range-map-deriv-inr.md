# The range map's derivative in the essential component is A

Let $E$, $Y$ and $\Lambda$ be real normed spaces, let $L : E \to Y$ be a bounded linear map, and fix
a Fredholm package of $L$: decompositions $E = X_1 \oplus X_0$ and $Y = Y_1 \oplus Y_0$ into
topologically complementary subspaces with $X_0$ and $Y_0$ finite-dimensional, and an isomorphism
$A : X_1 \to Y_1$ of normed spaces, such that $L x = A(\pi_1 x)$ for every $x$, where $\pi_1$ is the
projection onto $X_1$ along $X_0$. Then $\ker L = X_0$ and $\operatorname{range} L = Y_1$. Write $Q$
for the projection of $Y$ onto $Y_1$ along $Y_0$.

Let $F' : E \times \Lambda \to Y$ be a bounded linear map with $F'(x, 0) = L x$ for every $x \in E$.
Then the linear map $((z, p), w) \mapsto Q\, F'(z + w, p)$, restricted to the essential component
$w \in X_1$, is the package isomorphism: $Q\, F'(w, 0) = A w$. When $F'$ is the derivative of $F$ at
$(0, p_0)$, this is the partial derivative of the [range equation](ls-range-map.md) in $w$, which is
invertible.
