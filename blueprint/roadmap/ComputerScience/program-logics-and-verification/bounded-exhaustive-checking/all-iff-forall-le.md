# Bounded-exhaustive checking is exact under exact support

Let $\mathit{enum} : \mathbb{N} \to \mathrm{List}\,\alpha$ be an enumerator, $\mathit{size} : \alpha \to \mathbb{N}$, $p : \alpha \to \mathrm{Bool}$ and $n \in \mathbb{N}$. If the enumeration at bound $n$ has exact support, $x \in \mathit{enum}(n) \iff \mathit{size}(x) \le n$ for all $x$, then $p$ holds on every element of the list $\mathit{enum}(n)$ if and only if $p(x) = \mathrm{true}$ for every $x$ with $\mathit{size}(x) \le n$.
