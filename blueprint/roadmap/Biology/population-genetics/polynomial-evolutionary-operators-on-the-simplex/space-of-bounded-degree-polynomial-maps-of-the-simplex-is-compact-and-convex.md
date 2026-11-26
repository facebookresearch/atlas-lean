# Space of bounded-degree polynomial maps of the simplex is compact and convex

Let $\Delta^n=\{x\in\mathbb{R}^n: x_i\ge0,\ \sum_{i=1}^nx_i\le1\}$ be the frequency simplex of $n+1$ types (the last frequency is $1-\sum_ix_i$), and let $\Pi^n_k$ be the real vector space of polynomials in $n$ variables of degree at most $k$. Let $\mathsf{PMaps}(\Delta^n,k)$ be the set of maps $f=(P_1,\dots,P_n)$ with $P_i\in\Pi^n_k$ and $f(\Delta^n)\subseteq\Delta^n$, i.e.

$$
P_i(x)\ge0\quad(1\le i\le n),\qquad 1-\sum_{i=1}^nP_i(x)\ge0\qquad\text{for all }x\in\Delta^n .
$$

Such maps include the one-generation operators of population-genetic models with mutation, recombination and weak selection, and, for $k=1$, the transition maps of finite Markov chains.

**Theorem.** $\mathsf{PMaps}(\Delta^n,k)$ is a compact convex subset of the finite-dimensional vector space $\bigoplus_{i=1}^n\Pi^n_k$.

Its interior consists of maps all of whose defining polynomials $P_1,\dots,P_n,\,1-\sum_jP_j$ are strictly positive on $\Delta^n$ (images in the open simplex); boundary maps have some defining polynomial vanishing on an algebraic subset of $\Delta^n$. For $k=1$ the set is an $n(n+1)$-dimensional polytope of stochastic matrices, and the only bijective maps in it are the permutation matrices.

## Expansion

Polynomials in $\Pi^n_k$ that are strictly positive on $\Delta^n$ form an open convex cone (by Pólya's theorem, positivity is certified by positive coefficients of $(x_1+\dots+x_{n+1})^NP_H$ for the degree-$k$ homogenization $P_H$), and its closure is the cone $\mathcal K(\Delta^n,k)$ of polynomials nonnegative on $\Delta^n$. So the first conditions place $f$ in the closed convex cone $\mathcal K(\Delta^n,k)^n$. On each ray $\lambda(P_1,\dots,P_n)$ of that cone, the condition $1-\lambda\sum_iP_i\ge0$ on $\Delta^n$ holds exactly for $\lambda\in[0,1/S_{\max}]$, where $S_{\max}=\max_{\Delta^n}\sum_iP_i>0$; hence the set is closed and bounded, so compact by Heine–Borel. Convexity holds because $\Delta^n$ is convex: if $f(x),g(x)\in\Delta^n$ then $tf(x)+(1-t)g(x)\in\Delta^n$.

## Sources

- Sergio Lukic, *A note on the space of evolutionary operators in population genetics and folding dynamics*, arXiv:1305.0151 (2013), Theorem 1 (Section 2) and Lemma 1 (Appendix). <https://doi.org/10.48550/arXiv.1305.0151>
