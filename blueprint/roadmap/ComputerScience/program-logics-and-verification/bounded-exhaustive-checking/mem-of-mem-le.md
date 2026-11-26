# Exact-support enumerations are monotone in the bound

Let $\mathit{enum} : \mathbb{N} \to \mathrm{List}\,\alpha$ and $\mathit{size} : \alpha \to \mathbb{N}$ have exact support at every bound: $x \in \mathit{enum}(n) \iff \mathit{size}(x) \le n$ for all $n$ and $x$. Then for $m \le n$, every $x \in \mathit{enum}(m)$ also belongs to $\mathit{enum}(n)$.
