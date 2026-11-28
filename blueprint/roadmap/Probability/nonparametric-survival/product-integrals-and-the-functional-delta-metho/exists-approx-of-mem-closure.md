# Uniform approximation of paths in the closure of the bounded-variation paths

Let $\tau \in \mathbb{R}$ and let $\ell^\infty([0, \tau])$ be the space of bounded real functions on $[0, \tau]$ with the sup norm. For $h \in \ell^\infty([0, \tau])$ let $\bar h : \mathbb{R} \to \mathbb{R}$ be its extension by $0$ outside $[0, \tau]$. For functions $A, V : \mathbb{R} \to \mathbb{R}$ and reals $a, b$, say that $V$ is a control for $A$ on $[a, b]$ if $|A(x) - A(y)| \le V(x) - V(y)$ for all $a \le y \le x \le b$. The [bounded-variation paths](bv-paths.md) are the $y \in \ell^\infty([0, \tau])$ for which $\bar y$ has a control on $[0, \tau]$.

Let $h$ belong to the closure, in the sup norm, of the set of bounded-variation paths, and let $\varepsilon > 0$. Then there are functions $g, U : \mathbb{R} \to \mathbb{R}$ such that $U$ is a control for $g$ on $[0, \tau]$ and $|\bar h(x) - g(x)| \le \varepsilon$ for every $x \in \mathbb{R}$.
