# Asymptotic count of one-component tree-child networks

**Setting.** A (rooted, binary) phylogenetic network with $n$ leaves is a connected directed acyclic graph without parallel edges whose nodes are a root of in-degree $0$ and out-degree $1$, $n$ leaves of in-degree $1$ and out-degree $0$ labelled bijectively by $\{1,\dots,n\}$, tree nodes (in-degree $1$, out-degree $2$) and reticulation nodes (in-degree $2$, out-degree $1$). It is **tree-child** if every non-leaf node has a child that is not a reticulation node, and **one-component** if, in addition, every reticulation node is immediately followed by a leaf. Write $1\text{-}\mathrm{TC}_{n,k}$ for the number of one-component tree-child networks with $n$ leaves and $k$ reticulation nodes, and $1\text{-}\mathrm{TC}_n=\sum_k 1\text{-}\mathrm{TC}_{n,k}$.

**Exact formula (Cardona and Zhang).** For $0\le k\le n-1$,

$$
1\text{-}\mathrm{TC}_{n,k}=\binom{n}{k}\frac{(2n-2)!}{2^{n-1}(n-k-1)!}.
$$

**Theorem (leaf-labelled asymptotics).** As $n\to\infty$,

$$
1\text{-}\mathrm{TC}_n\sim\frac{1}{2\sqrt e}\,n^{-5/4}\,e^{2\sqrt n}\left(\frac{2}{e^2}\right)^{n}n^{2n}.
$$

**Theorem (node-labelled asymptotics).** Let $1\text{-}\widehat{\mathrm{TC}}_N$ count one-component tree-child networks whose $N$ non-root nodes are all bijectively labelled ($N$ odd). Then

$$
1\text{-}\widehat{\mathrm{TC}}_N=\sum_{n=\lceil (N+3)/4\rceil}^{(N+1)/2}\binom{N}{n}(N-n)!\;1\text{-}\mathrm{TC}_{n,(N+1)/2-n},
$$

and, as $N\to\infty$ through odd integers,

$$
1\text{-}\widehat{\mathrm{TC}}_N\sim 2^{9/8}e^{-1/32}N^{-7/8}\exp\!\left(\frac{(2N)^{3/4}}{2}+\frac{\sqrt{2N}}{16}-\frac{3(2N)^{1/4}}{64}\right)\left(\frac{1}{2e^5}\right)^{N/4}N^{5N/4}.
$$

Compared with all tree-child networks, whose leaf-labelled count grows like $n^{-2/3}e^{a_1(3n)^{1/3}}(12/e^2)^n n^{2n}$ (with $a_1$ the largest zero of the Airy function), the one-component class shares the factor $n^{2n}$ but has a much smaller exponential rate and a stretched exponential $e^{2\sqrt n}$ instead of $e^{a_1(3n)^{1/3}}$.

## Expansion

Writing $1\text{-}\mathrm{TC}_n=\frac{n!(2n-2)!}{2^{n-1}}\sum_{k=0}^{n-1}\frac{1}{k!(n-k)!(n-k-1)!}$, Stirling's formula gives $\frac{n!(2n-2)!}{2^{n-1}}\sim\sqrt2\,\pi\,n^{-1}(2/e^3)^n n^{3n}$. The summand is unimodal with peak near $k=n-\sqrt n$; with $k=n-\sqrt n+x$ it equals $\frac{1}{2\pi\sqrt{2e\pi}}n^{-1/2}e^{2\sqrt n}(e/n)^n e^{-x^2/\sqrt n}(1+o(1))$ uniformly for $|x|\le n^{3/8}$. The Laplace method (a Gaussian sum of width $n^{1/4}$) yields the sum's asymptotics and hence the leaf-labelled result. The $e^{2\sqrt n}$ factor comes from the reticulation count concentrating at $n-\sqrt n$ rather than at its maximum $n-1$.

For node labels, distinct non-root nodes of a tree-child network have distinct descendant leaf sets, and $n+k=(N+1)/2$; so one chooses which $n$ labels go to leaves (order-preservingly) and distributes the remaining $N-n$ labels freely, giving the displayed sum. Its terms peak at $n\approx N/4+(2N)^{3/4}/8+\sqrt{2N}/32-9(2N)^{1/4}/256$, and a second Laplace-method computation produces the three stretched exponentials.

## Sources

- Michael Fuchs, Guan-Ru Yu, Louxin Zhang, "On the asymptotic growth of the number of tree-child networks", European Journal of Combinatorics 93 (2021), 103278, <https://doi.org/10.1016/j.ejc.2020.103278>. Published version of arXiv:2003.08049, cited next; locators there refer to the arXiv version.
- Michael Fuchs, Guan-Ru Yu and Louxin Zhang, "On the Asymptotic Growth of the Number of Tree-Child Networks", arXiv (2020): Definition 1 and Definition 3 (tree-child and one-component networks), Theorem 2 (exact formula, after Cardona and Zhang), Theorem 3 (leaf-labelled asymptotics), Theorem 4 (node-labelled asymptotics), Theorem 1 (for the comparison with all tree-child networks). <https://doi.org/10.48550/arXiv.2003.08049>
