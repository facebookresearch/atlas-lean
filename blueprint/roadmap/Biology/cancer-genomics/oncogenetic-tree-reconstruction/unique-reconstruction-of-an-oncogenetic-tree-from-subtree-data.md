# Unique reconstruction of an oncogenetic tree from tumour mutation sets

**Setting (oncogenetic trees).** An oncogenetic tree is a rooted directed tree $T=(V,E,r)$ (every vertex has in-degree at most one, no cycles). The root $r$ is the mutation-free tissue state and every other vertex is a genetic event; an edge $(u,v)$ means that $v$ can occur only if $u$ has occurred, so a tumour's set of events is the vertex set of an $r$-rooted subtree of $T$. Write $u\prec v$ when $u$ is a descendant of $v$. The data are a finite family $\mathcal F=\{A_1,\dots,A_q\}$ of such vertex sets, one per tumour.

**Theorem 1.** $T$ is uniquely determined by $\mathcal F$ (among all rooted trees for which every $A_i$ is the vertex set of a rooted subtree) if and only if:

1. for every edge $(x,y)\in E(T)$ there is $A_i\in\mathcal F$ with $x\in A_i$ and $y\notin A_i$;
2. for every pair of distinct vertices $x,y$ with $x\not\prec y$ and $y\not\prec x$, there are $A_i,A_j\in\mathcal F$ with $x\in A_i$, $y\notin A_i$ and $y\in A_j$, $x\notin A_j$.

Under these conditions, for every vertex $x$ the intersection of all observed sets containing $x$,

$$F_x=\bigcap_{A_i\ni x}A_i ,$$

equals the vertex set $P_x$ of the path from $r$ to $x$, and the order along each path is read off from sets containing one vertex but not its successor. This gives a direct reconstruction algorithm.

## Expansion

Necessity: if condition 1 fails for an edge $(x,y)$, every observed set contains both or neither, so the tree with $x$ and $y$ swapped is equally consistent. If condition 2 fails for incomparable $x,y$ because every set containing $x$ also contains $y$, the tree with $x$ re-attached below $y$ is consistent too. Sufficiency: always $P_x\subseteq F_x$. A vertex $v\in F_x\setminus P_x$ is either a descendant of $x$, excluded by applying condition 1 along the path from $x$ to $v$, or incomparable with $x$, excluded by condition 2; ancestors of $x$ already lie in $P_x$. Hence $F_x=P_x$, and condition 1 orders each path. The result answers when noise-free tumour profiles determine a progression model of the Desper et al. type; real array data are noisy and typically consistent with several trees, which is why likelihood and probability-raising estimators are used in practice.

## Sources

- Charalampos E. Tsourakakis, "Perfect reconstruction of oncogenetic trees", arXiv:1201.4618 (2012), Section 1 (definition of oncogenetic trees, Theorem 1) and Section 2 (proof and reconstruction procedure), <https://doi.org/10.48550/arXiv.1201.4618>.
