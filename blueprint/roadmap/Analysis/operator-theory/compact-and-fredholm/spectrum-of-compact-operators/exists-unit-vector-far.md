# Riesz separation for nested spans

Let $E$ be a normed space over
$\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $(u_n)_{n \in \mathbb{N}}$ be vectors in $E$, and
for each $n$ let $V_n$ be the linear span of $\{u_i : i < n\}$. Suppose $u_n \notin V_n$ for
every $n$. Then for every $n$ there is a vector $y \in V_{n+1}$ with $\|y\| = 1$ and
$\|y - z\| \ge 1/2$ for every $z \in V_n$.

This is Riesz's lemma for the finite-dimensional, hence closed, subspace $V_n$: one takes $y$ to be
the normalization of $u_n - z$ for a $z \in V_n$ almost realizing the distance $d > 0$ from
$u_n$ to $V_n$.
