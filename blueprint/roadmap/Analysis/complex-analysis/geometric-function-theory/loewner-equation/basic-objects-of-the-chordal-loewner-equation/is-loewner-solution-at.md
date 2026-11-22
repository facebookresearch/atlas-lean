# Solution of the Loewner equation at a time

Let $W : \mathbb{R} \to \mathbb{R}$ be a driving function and $(g_s)_{s \in \mathbb{R}}$ a family of maps $\mathbb{C} \to \mathbb{C}$. For $z \in \mathbb{C}$ and $t \in \mathbb{R}$, the trajectory $s \mapsto g_s(z)$ solves the Loewner equation at time $t$ if it is differentiable at $t$ with

$$
\partial_t g_t(z) = \frac{2}{g_t(z) - W(t)},
$$

the right side being the [Loewner vector field](loewner-field.md), with the convention $2/0 = 0$ when $g_t(z) = W(t)$.
