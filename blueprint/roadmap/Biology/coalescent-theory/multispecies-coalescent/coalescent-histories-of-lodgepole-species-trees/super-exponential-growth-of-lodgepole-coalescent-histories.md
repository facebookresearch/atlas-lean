# Super-exponential growth of coalescent histories for lodgepole species trees

**Coalescent histories.** For a rooted binary species tree $t$ and a gene tree with the same labeled topology, a **matching coalescent history** is a map $h$ from the internal nodes of $t$ to the branches of $t$ such that (a) every leaf descended from internal node $k$ is descended from branch $h(k)$, and (b) whenever internal node $k_2$ descends from $k_1$, branch $h(k_2)$ descends from or equals branch $h(k_1)$. It records on which species-tree branch each gene-tree coalescence occurs; gene-tree probabilities under the multispecies coalescent are sums over such histories.

**Lodgepole species trees.** Let $\lambda_0$ be the one-taxon tree and let $\lambda_{n+1}$ join $\lambda_n$ and a two-leaf cherry at a common root. Thus $\lambda_n$ has $m=2n+1$ taxa: a main branch carrying $n$ internal nodes, each with a cherry attached.

**Proposition.** Let $h_n$ be the number of matching coalescent histories of $\lambda_n$, with $h_0=1$. Then for $n\ge1$

$$
h_n=(2n+1)!!-\sum_{k=0}^{n-1}(2k+1)!!\,h_{n-1-k},
$$

with the bounds

$$
(2n+1)!!\,\frac{n-2}{n}\le h_n\le(2n+1)!!,
$$

and therefore

$$
h_n\sim(2n+1)!!\sim\sqrt2\left[\frac{2(n+1)}{e}\right]^{n+1}.
$$

Equivalently, $h_n=\sum_{\bar a\in V_n}\prod_{i=1}^n a_i$ over integer vectors with $a_1=2$ and $2\le a_i\le a_{i-1}+1$, and $h_n$ is the number of indecomposable histoires d'Hermite of size $n+1$. The first values are $h_1=2$, $h_2=10$.

**Corollary (growth in the number of taxa).** For odd $m$, $h_{(m-1)/2}\sim m!!\sim\sqrt2\,\big(\sqrt{(m+1)/e}\big)^{m+1}$. So, unlike caterpillar species trees, whose matching histories grow exponentially (Catalan numbers), some species-tree families have super-exponentially many coalescent histories.

**Corollary (spread across topologies).** Let $R(m)=h_m^+/h_m^-$ be the ratio of the largest to the smallest number of matching coalescent histories among $m$-taxon species trees. For odd $m\ge7$,

$$
R(m)\ge\left(\frac{\sqrt{m-1}}{4\sqrt e}\right)^{m},
$$

improving the earlier bound of order $m\sqrt m$.

## Depends on

- [The multispecies coalescent](../gene-tree-prob.md)

## Expansion

A history of $\lambda_n$ is built by first mapping the $n$ main-branch nodes (from the root downward) and then placing each cherry node on a branch no higher than the image of its parent; counting choices gives the vector formula, where $a_i$ counts the admissible branches for cherry $i$. The vectors $\bar a\in V_n$ biject with Dyck paths of size $n$ via $a_i=y_i+1$ ($y_i$ the height after the $i$-th up-step), and labeling up-step $i$ by an integer in $[1,y_i+1]$ turns $h_n$ into a count of labeled Dyck paths. Prepending an up-step and appending a down-step maps these bijectively to indecomposable histoires d'Hermite of size $n+1$. All histoires of size $k$ number $(2k-1)!!$, and decomposing a decomposable histoire at its first return to the axis yields the recursion. Bounding $h_{n-1-k}\le(2(n-1-k)+1)!!$ in the recursion gives $1-s_n\le h_n/(2n+1)!!\le1$ with $s_n=\sum_{k=0}^{n-1}\binom{n+1}{k+1}/\binom{2n+2}{2k+2}$, and $(2n+3)s_{n+1}=(n+2)s_n+1$ implies $s_n\le 2/n$. For $R(m)$, combine this lower bound on $h_m^+$ with the bicaterpillar upper bound $h_m^-\le c_nc_{n+1}$ (Catalan numbers).

## Sources

- Filippo Disanto and Noah A. Rosenberg, *Coalescent histories for lodgepole species trees*, J. Comput. Biol. 22(10) (2015), 918–929. <https://doi.org/10.1089/cmb.2015.0015> Section 2 (matching coalescent histories, the lodgepole family, Dyck paths), Section 3 (the vector formula, the correspondence with histoires d'Hermite, Proposition 1, Corollary 1 and Corollary 2). Locators use the numbering of the preprint arXiv:1503.03560.
