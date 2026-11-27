# Asymptotic enumeration of galled tree-child networks

**Definitions.** A (rooted binary) phylogenetic network of size $n$ is a rooted simple DAG with a root of indegree $0$ and outdegree $1$, $n$ leaves bijectively labeled by $[n]$, and internal nodes that are either *tree nodes* (indegree $1$, outdegree $2$) or *reticulation nodes* (indegree $2$, outdegree $1$). It is *tree-child* if every non-leaf node has a child that is a tree node or a leaf, and *galled* if every reticulation node lies in a (necessarily unique) tree cycle. A *galled tree-child network* is one that is both; neither of the two parent classes contains the other. Let $\mathrm{GTC}_n$ count galled tree-child networks of size $n$, $\mathrm{GTC}_{n,k}$ those with $k$ reticulations, and $R_n$ the number of reticulations of a uniformly random one.

**Theorem.**

1. A galled tree-child network of size $n$ has at most $n-1$ reticulations (sharp), and as $n\to\infty$

$$\mathrm{GTC}_n\sim\frac{1}{2\sqrt[4]{e}}\,n^{-5/4}\,e^{2\sqrt n}\Bigl(\frac{2}{e^2}\Bigr)^n n^{2n} .$$

2. The maximally reticulated ones satisfy $\mathrm{GTC}_{n,n-1}\sim\sqrt{e\pi}\,n^{-1/2}(2/e^2)^n n^{2n}$, so unlike tree-child networks, $\mathrm{GTC}_n$ is not of the order of its maximally reticulated subclass.
3. For fixed $k$,

$$\mathrm{GTC}_{n,k}\sim\frac{2^{k-1}\sqrt2}{k!}\Bigl(\frac2e\Bigr)^n n^{\,n+2k-1}.$$

4. *(Reticulation count.)* $(R_n-\mathbb E R_n)/\sqrt{\operatorname{Var}R_n}\to N(0,1)$ with $\mathbb E R_n\sim n-\sqrt n$ and $\operatorname{Var}R_n\sim\sqrt n/2$. More precisely, if $I_n$ counts reticulations not followed by a leaf,

$$\Bigl(I_n,\ \frac{R_n-n+\sqrt n}{\sqrt[4]{n/4}}\Bigr)\xrightarrow{d}(I,R),\qquad I\sim\mathrm{Poisson}(1/4),\ R\sim N(0,1)\ \text{independent}.$$

The counts begin $1,3,48,1611,87660,6891615,\dots$ for $n=1,2,\dots$

## Expansion

Collapsing each tree cycle gives the component graph, which for a galled network is a (not necessarily binary) phylogenetic tree; summing over such trees with, at each internal node, the number of one-component galled tree-child networks on its children gives an exact formula for $\mathrm{GTC}_n$. Every one-component tree-child network is galled, so the one-component counts are the known $\mathrm{OTC}_{n,k}=\binom nk\frac{(2n-2)!}{2^{n-1}(n-k-1)!}$, whose peak at $k\approx n-\sqrt n$ produces the stretched exponential $e^{2\sqrt n}$. The tree decomposition becomes a functional equation $U(z)=z+U(z)A(U(z))$ for exponential generating functions with zero radius of convergence, handled by Bender's theorem on coefficients of compositions $z^n)^{\alpha n+\beta}\sim\alpha e^{\alpha s_1\gamma}ns_n$. The Gaussian limit with $n^{1/4}$ scaling contrasts with the discrete limit law of reticulations in random galled networks.

## Sources

- Yu-Sheng Chang, Michael Fuchs, Guan-Ru Yu, "Galled tree-child networks", in 35th International Conference on Probabilistic, Combinatorial and Asymptotic Methods for the Analysis of Algorithms (AofA 2024), Leibniz International Proceedings in Informatics 302 (2024), 8:1–8:13, <https://doi.org/10.4230/LIPIcs.AofA.2024.8>. Published version of arXiv:2403.02923, cited next; locators there refer to the arXiv version.
- Y.-S. Chang, M. Fuchs, G.-R. Yu, "Galled Tree-Child Networks", arXiv:2403.02923 (2024), Definitions 1.1–1.5, Theorems 1.6 and 1.8, Propositions 2.5 and 2.7, Lemma 3.1, Theorems 3.4, 3.6 and 4.5. <https://doi.org/10.48550/arXiv.2403.02923>
