# Passing a bounded check implies bounded validity

Let $\mathit{enum} : \mathbb{N} \to \mathrm{List}\,\alpha$, $\mathit{size} : \alpha \to \mathbb{N}$, $p : \alpha \to \mathrm{Bool}$ and $n \in \mathbb{N}$. If the enumeration at bound $n$ is complete, every $x$ with $\mathit{size}(x) \le n$ belongs to $\mathit{enum}(n)$, and $p$ holds on every element of $\mathit{enum}(n)$, then $p(x) = \mathrm{true}$ for every $x$ with $\mathit{size}(x) \le n$. No soundness assumption (that $\mathit{enum}(n)$ contains only elements of size at most $n$) is needed.
