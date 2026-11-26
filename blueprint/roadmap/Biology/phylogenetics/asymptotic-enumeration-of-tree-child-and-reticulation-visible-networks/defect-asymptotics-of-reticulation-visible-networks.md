# Defect asymptotics of reticulation-visible networks

**Setting.** In a binary phylogenetic network on $[n]$ (root of out-degree one), a vertex is *visible* if some leaf is reached from the root only through it, and the network is **reticulation-visible** if every reticulation is visible. Let $\operatorname{RV}_{n,r}$ count binary reticulation-visible networks with $n$ leaves and $r$ reticulations; then $r\le3n-3$. Measure the distance from this maximum by the defect $q=3n-3-r$ and set

$$
V_{n,q}=\operatorname{RV}_{n,3n-3-q},\qquad Z_n(z)=\frac{1}{M_n}\sum_{q=0}^{3n-3}V_{n,q}z^q,
$$

where $M_n$ is the number of maximally reticulated tree-child networks with $n$ leaves. Removing the incoming arcs of every reticulation and compressing components gives a skeleton built on a maximal tree-child network; $Z_n^{(0)}$ denotes the part of $Z_n$ whose normalized skeleton is maximal.

**The $5/8$ law.** In a uniformly random maximal tree-child network on $[n]$, the number $L$ of leaves whose parent is a tree vertex satisfies $\mathbb E|L/n-5/8|=O(n^{-1/3})$, and $L/n\to5/8$ in probability and in every fixed moment.

**Bounded sector comparison.** For every $n\ge2$,

$$
Z_n^{(0)}(1)\le Z_n(1)<30\,Z_n^{(0)}(1),
$$

so a uniformly random binary reticulation-visible network on $[n]$ has a maximal normalized skeleton with probability greater than $1/30$; for every $z>0$ the ratio $Z_n(z)/Z_n^{(0)}(z)$ is bounded uniformly in $n$.

**Theorem (microscopic defects).** For every $R>0$, uniformly for complex $|t|\le R$,

$$
Z_n(t/n)=e^{19t/4}+O_R(n^{-1/3}).
$$

Consequently, for every fixed $q\ge0$, $V_{n,q}/(M_nn^q)=(19/4)^q/q!+O_q(n^{-1/3})$; in particular $V_{n,2}=\frac{361}{32}n^2M_n(1+O(n^{-1/3}))$. Under the law giving defect $q$ probability proportional to $V_{n,q}(t/n)^q$, the defect is within total variation $O_t(n^{-1/3})$ of $\operatorname{Poisson}(19t/4)$, and if $Q_n=o(n^{1/3})$ then uniformly for $0\le q\le Q_n$,

$$
V_{n,q}=M_n\,\frac{((19/4)n)^q}{q!}\,(1+o(1)).
$$

**Theorem (pressure and total growth).** For every compact $\mathcal K\subset(0,\infty)$ there is an analytic pressure $\psi$ with $\log Z_n(z)=n\psi(z)+O_{\mathcal K}(n^{2/3}\log^{2/3}(n+2))$ for $z\in\mathcal K$. For the total count $\operatorname{RV}_n=\sum_r\operatorname{RV}_{n,r}$,

$$
\log\operatorname{RV}_n=2n\log n+n\log\frac{\Lambda(1)}{e^2}+O\bigl(n^{2/3}\log^{2/3}(n+2)\bigr),\qquad \frac{\Lambda(1)}{e^2}=13.9657067341\ldots,
$$

where $\psi(z)=\log(\Lambda(z)/12)$ is given by an explicit variational formula for the kernel $\mathcal C(x;z)=\frac{1-2zx}{(1-2zx)^{3/2}-x}$. Every mode $q_n$ of $(V_{n,q})_q$ satisfies $q_n/n\to\psi'(1)=1.1969529048\ldots$, and $Q_n/n$ satisfies a full large-deviation principle with speed $n$.

## Depends on

- [Airy amplitude of maximal and total tree-child network counts](airy-amplitude-of-maximal-and-total-tree-child-network-counts.md)

## Expansion

The component construction expands each reticulation-visible network from a maximal tree-child network by partitioning the tree paths into consecutive blocks, with explicit local block weights; this exact refinement writes $Z_n(z)$ as an expectation over uniform maximal tree-child networks. The total defect splits into a skeleton defect, an arity excess and an ordinary-leaf count. A weighted factorial-moment bound shows the skeleton defect has a uniformly bounded exponential moment, which gives the bounded comparison (the constant $30$ is certified by rational interval arithmetic at $z=1$). At activity $z=t/n$ only single-step defects matter, each available at a rate determined by the leaf statistics of the skeleton; the $5/8$ law for leaves turns the expected rate into $19/4$, giving the Poisson limit. At fixed activity the weighted words have a quantitative Laplace principle whose variational problem is solved explicitly, which yields the pressure, the modes and the large deviations.

## Sources

- Miquel Pons Viver, "Counting tree-child and reticulation visible networks", arXiv (2026), Section 7 (Theorem 7.1, Corollary 7.5), Section 8 (Theorem 8.1), Section 9 (Theorem 9.4, Corollaries 9.5–9.6, Theorem 9.7) and Sections 11–12 (Theorem 11.1, Theorem 11.4, Theorem 12.1), <https://doi.org/10.48550/arXiv.2611.32460>
