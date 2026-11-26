# An operator acts as a scalar on a span of eigenvectors modulo a smaller span

Let $E$ be a
normed space over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$, let $T$ be a bounded linear operator
on $E$, let $(\lambda_n)_{n \in \mathbb{N}}$ in $\mathbb{K}$ and $(u_n)_{n \in \mathbb{N}}$ in $E$
satisfy $T u_n = \lambda_n u_n$ for every $n$, and for each $n$ let $V_n$ be the linear span of
$\{u_i : i < n\}$. Then for every $n$ and every $y \in V_{n+1}$, we have
$T y - \lambda_n y \in V_n$.

The proof is induction on the span: each generator $u_i$ with $i < n$ contributes
$(\lambda_i - \lambda_n) u_i$ and the generator $u_n$ contributes $0$.
