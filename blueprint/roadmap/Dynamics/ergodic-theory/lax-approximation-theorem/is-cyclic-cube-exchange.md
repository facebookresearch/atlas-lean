# Cyclic cube exchange

Let $n$ and $d$ be natural numbers. For an index
$k \in \{0, \dots, n-1\}^d$, the grid cube with index $k$ is the set of points of the torus
$\mathbb{T}^d = (\mathbb{R}/\mathbb{Z})^d$ whose $i$-th coordinate is the class of a real
number in $[k_i/n, (k_i + 1)/n)$ for every $i < d$. A measurable, invertible,
volume-preserving transformation $T$ of $\mathbb{T}^d$ is a cyclic cube exchange with $n$
subdivisions if $n > 0$ and there is a permutation $\sigma$ of $\{0, \dots, n-1\}^d$ that is
a single cycle moving every index, such that for every index $k$, every point $x$ of the
grid cube with index $k$ and every $i < d$, we have
$(T x)_i = x_i + (\sigma(k)_i - k_i)/n$ in $\mathbb{R}/\mathbb{Z}$. Thus $T$ translates each
grid cube $k$ rigidly onto the grid cube $\sigma(k)$.
