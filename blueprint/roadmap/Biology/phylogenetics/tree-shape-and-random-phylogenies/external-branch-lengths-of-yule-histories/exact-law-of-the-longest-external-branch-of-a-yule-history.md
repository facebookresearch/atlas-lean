# Exact law of the longest external branch of a Yule history

A **history** of size $n$ is a full binary rooted tree with $n$ leaves whose $n-1$ internal nodes carry distinct ranks $1,\dots,n-1$, decreasing along every root-to-leaf path (the root has rank $n-1$). The **length** of an external branch (a branch ending in a leaf) is the rank of its parent node. Under the **Yule model**, a history of size $n$ is the shape of a uniformly random *ordered* (plane-embedded) history of size $n$; there are $(n-1)!$ ordered histories, and a history $t$ with $c(t)$ cherries has Yule probability $2^{n-1-c(t)}/(n-1)!$.

Order the distinct external branch lengths of a random history as $\ell_1 > \ell_2 > \cdots$. For $n \ge 3$:

1. **Distribution function.** For $\lceil n/2 \rceil \le u \le n-1$,

$$\Pr(\ell_1 \le u) = \frac{u!\,(u-1)!}{(2u-n)!\,(n-1)!}.$$

2. **Point probabilities.** For $\lceil n/2 \rceil \le s \le n-1$,

$$\Pr(\ell_1 = s) = \frac{(s-1)!\,(s-2)!\,\bigl(4ns + s - n^2 - n - 3s^2\bigr)}{(2s-n)!\,(n-1)!}.$$

3. **Recurrence for the joint law.** For $n > s_1 > s_2 > \cdots > s_k$, writing $p_n(\cdot)$ for probabilities over Yule histories of size $n$,

$$p_n(\ell_1=s_1,\dots,\ell_k=s_k) = \frac{2(n-s_1)}{n-1}\,p_{n-1}(\ell_1=s_2,\dots,\ell_{k-1}=s_k) + \frac{(n-s_1)(n-s_1-1)}{(n-1)(n-2)}\,p_{n-2}(\ell_1=s_2,\dots,\ell_{k-1}=s_k),$$

with initial condition the formula in item 2. Summing over $s_1,\dots,s_{k-1}$ gives the marginal law of $\ell_k$.

The range is sharp: $\ell_1 \ge \lceil n/2 \rceil$ always and $\ell_1 \le n-1$, the maximum being attained when a child of the root is a leaf.

## Depends on

- [Ranked labeled history](../../../coalescent-theory/ranked-labeled-histories-of-coalescent-trees/ranked-history.md)

## Proof sketch

The proof passes through permutations. The classical bijection $t \mapsto \pi_t = (\pi_{t_L}, r(t), \pi_{t_R})$ (in-order reading of node ranks) sends ordered histories of size $n$ to permutations of $\{1,\dots,n-1\}$; an internal node is the parent of a leaf exactly when its rank is a *non-peak* entry of $\pi_t$, so $\ell_k$ is the $k$th largest non-peak entry. A known recursion for the number of permutations with a prescribed peak set gives the counts $h_n$ of ordered histories with prescribed largest external lengths:

$$h_{n+1}(\ell_1=s) = 2(n-s+1)\,h_n(\ell_1<s) + (n-s)(n-s+1)\,h_{n-1}(\ell_1<s),$$

and $h_n(\ell_1<s) = (s-1)!\,(s-2)!/(2s-n-2)!$ is verified by checking that it satisfies the induced recurrence with the boundary values $0$ at $s=\lceil n/2\rceil$ and $(n-1)!$ at $s=n$. Dividing by $(n-1)!$ gives items 1–3. Biologically, external branches carry the singleton mutations of the site frequency spectrum under the infinite-sites model, so $\ell_1$ measures the layer depth over which the most singleton-rich gene copy has been accumulating private mutations.

## Sources

- Filippo Disanto and Michael Fuchs, "Distribution of External Branch Lengths in Yule Histories", *The Electronic Journal of Combinatorics* 30 (2023), P3.23, <https://doi.org/10.37236/11438>. Preprint version: arXiv:2208.04804 (2022), Section 3, Proposition 1, and the distribution function displayed at the start of Section 4, <https://doi.org/10.48550/arXiv.2208.04804>.
