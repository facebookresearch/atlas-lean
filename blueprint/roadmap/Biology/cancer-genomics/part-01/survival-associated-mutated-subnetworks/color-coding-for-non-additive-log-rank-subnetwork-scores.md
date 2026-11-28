# Color-coding for non-additive log-rank subnetwork scores

**Algorithm.** Color the vertices of the interaction graph $G=(V,E)$ uniformly at random with $k$ colors. For each nonempty colorset $T\subseteq\{1,\dots,k\}$ and vertex $u$, a table entry $W(T,u)$ stores one connected colorful subnetwork with colorset $T$ containing $u$: $W(\{C(u)\},u)=\{u\}$, and for $|T|\ge 2$,

$$
W(T,u)=\arg\max_{S\in S'(T,u)} w(S),\qquad S'(T,u)=\bigcup_{v:(u,v)\in E}\ \bigcup_{Q\sqcup R=T}\{W(Q,u)\cup W(R,v)\},
$$

where $w$ is the normalized log-rank score of the subnetwork. One coloring costs $O(m|E|4^k)$, and $L$ colorings cost $O(Lm|E|4^k)$.

**Statements.**

1. *Colorfulness is not sufficient.* For every $k\ge 3$ there are instances and colorings for which the optimum OPT is colorful but is not found. More strongly, for any optimal colorful connected subnetwork $S$ of size $k\ge 3$ and any color-coding algorithm that forms colorset size $i$ by merging two subnetworks of smaller colorset size, adding three suitably colored neighbors to $S$ can make the algorithm miss $S$.
2. *Planted subnetwork guarantee.* Suppose there is a connected $D$, $|D|=k$, with unnormalized score $w(D)\ge cm$ for a constant $c>0$; each $g\in D$ satisfies $w(D)-w(D\setminus\{g\})\ge c'm/k$ for a constant $c'>0$ and $w(\{g\})>0$; and every gene outside $D$ is mutated independently in each patient with its own probability, independently of survival and censoring. If, for a constant $\varepsilon>0$, $m\in\Omega\bigl(k^4(k+\varepsilon)\ln n\bigr)$ and $O(\ln(1/\delta)e^k)$ colorings are used, the algorithm returns $D$ with probability at least $1-n^{-\varepsilon}-\delta$.

## Expansion

For a set-additive score, keeping the best partial solution per (colorset, vertex) is exact once OPT is colorful, which happens with probability $k!/k^k\ge e^{-k}$. With the union-type log-rank score, the best partial subnetwork can share mutated patients with the rest of OPT and be dominated in the merge, so an adversary can make the dynamic program discard the right fragment. Under the planted model, every gene of $D$ contributes a linear-in-$m$ marginal gain while genes outside $D$ contribute only concentration-bounded noise; with enough samples, Hoeffding-type bounds and a union bound over the $n$ genes ensure that each sub-fragment of $D$ beats every competitor in its table cell, restoring the additive-case guarantee.

## Depends on

- [NP-hardness of the max connected k-set log-rank problem](np-hardness-of-the-max-connected-k-set-log-rank-problem.md)

## Sources

- Altieri F, Hansen TV, Vandin F. NoMAS: a computational approach to find mutated subnetworks associated with survival in genome-wide cancer studies. *Frontiers in Genetics* 10 (2019) 265. <https://doi.org/10.3389/fgene.2019.00265>. PMCID: PMC6468148. Section 2.2; Section 3.1, Proposition 1, Theorems 3 and 4.
