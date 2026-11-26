# The product $AP$ is identifiable iff $A(P\xi) = 0$ forces $\xi = 0$

For a real $m \times n$ matrix $A$ and a real $n \times d$ matrix $P$, the product $AP$ is
[identifiable](identifiable.md) ($\xi \mapsto (AP)\,\xi$ injective on $\mathbb{R}^d$) if and only
if

$$A(P\xi) = 0 \implies \xi = 0 \qquad \text{for every } \xi \in \mathbb{R}^d .$$

No condition is imposed on $P$. In the intended use the columns of $P$ are parameter directions
and $\xi$ are coordinates along them; the condition says that $P$ maps no nonzero coordinate
vector $\xi$ into the kernel of $A$, which in particular requires $P\xi = 0$ only for $\xi = 0$.
