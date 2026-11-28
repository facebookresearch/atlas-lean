# Ambainis adversary bound

Let $N\ge1$ be an integer, let $f : \{0,1\}^N \to \{0,1\}$ be a total Boolean function, let
$X \subseteq f^{-1}(0)$ and $Y \subseteq f^{-1}(1)$ be nonempty, and let $R \subseteq X \times Y$.
Let $m,m',\ell,\ell'$ be positive real numbers. Suppose every $x \in X$ is related to at least $m$
distinct inputs $y \in Y$, every $y \in Y$ to at least $m'$ distinct inputs $x \in X$, for every
$x \in X$ and index $i$ at most $\ell$ inputs $y$ related to $x$ satisfy $x_i \ne y_i$, and for every
$y \in Y$ and index $i$ at most $\ell'$ inputs $x$ related to $y$ satisfy $x_i \ne y_i$.
Then, for any fixed error bound $0\le\varepsilon<1/2$, every quantum query algorithm computing $f$
with error at most $\varepsilon$ on every input uses
$\Omega\big(\sqrt{m m'/(\ell \ell')}\big)$ queries in the worst case, with implicit constant depending
only on $\varepsilon$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Quantum query (oracle) model.

## Sources

- A. Ambainis, *Quantum lower bounds by quantum arguments*, J. Comput. System Sci. 64 (2002); arXiv:quant-ph/0002066, Theorem 2 and its proof (nonempty input sets and positive parameters make the displayed normalizations and ratios defined). <https://arxiv.org/pdf/quant-ph/0002066>
