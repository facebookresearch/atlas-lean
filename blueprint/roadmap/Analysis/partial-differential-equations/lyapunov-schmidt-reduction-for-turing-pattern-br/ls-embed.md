# Lyapunov–Schmidt ansatz (z, p, w) ↦ (z + w, p)

Let $E$, $Y$ and $\Lambda$ be real normed spaces, let $L : E \to Y$ be a bounded linear map, and fix
a Fredholm package of $L$: decompositions $E = X_1 \oplus X_0$ and $Y = Y_1 \oplus Y_0$ into
topologically complementary subspaces with $X_0$ and $Y_0$ finite-dimensional, and an isomorphism
$A : X_1 \to Y_1$ of normed spaces, such that $L x = A(\pi_1 x)$ for every $x$, where $\pi_1$ is the
projection onto $X_1$ along $X_0$. Then $\ker L = X_0$ and $\operatorname{range} L = Y_1$.

The ansatz is the bounded linear map $(X_0 \times \Lambda) \times X_1 \to E \times \Lambda$,
$((z, p), w) \mapsto (z + w, p)$: a state is a kernel component $z \in X_0$ plus an essential
component $w \in X_1$, together with the parameter $p \in \Lambda$.
