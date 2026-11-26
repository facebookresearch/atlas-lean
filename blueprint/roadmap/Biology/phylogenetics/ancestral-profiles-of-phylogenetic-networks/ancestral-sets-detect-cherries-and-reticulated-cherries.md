# Ancestral sets detect cherries and reticulated cherries

**Setting.** A (binary, rooted) phylogenetic network on $X$ is an acyclic digraph with a root of in-degree $0$ and out-degree $2$, leaves of in-degree $1$ and out-degree $0$ forming the set $X$, and all other vertices either tree vertices (in-degree $1$, out-degree $2$) or reticulations (in-degree $2$, out-degree $1$). For $x\in X$, the *ancestral set* is

$$ \gamma(x)=\{v\in V\setminus X : x \text{ is reachable from } v\} . $$

A $2$-element set $\{a,b\}\subseteq X$ is a *cherry* if $a,b$ have a common parent, and a *reticulated cherry with reticulation leaf $b$* if the parent $p_b$ of $b$ is a reticulation and $(p_a,p_b)$ is an arc.

**Lemma.** Let $N$ be a phylogenetic network on $X$ and $a\ne b$ in $X$.

1. $\gamma(a)\subseteq\gamma(b)$ if and only if the parent of $b$ is reachable from the parent of $a$.
2. $\{a,b\}$ is a cherry if and only if $\gamma(a)=\gamma(b)$.
3. $\{a,b\}$ is a reticulated cherry with reticulation leaf $b$ if and only if (i) $\gamma(a)\subsetneq\gamma(b)$, (ii) there is no $x\in X\setminus\{b\}$ with $\gamma(a)\subsetneq\gamma(x)$, and (iii) exactly one vertex lies in $\gamma(b)$ but in no $\gamma(x)$ with $x\in X\setminus\{b\}$.

## Expansion

Part 1 holds because $p_a\in\gamma(b)$ means $b$, hence $p_b$, is below $p_a$. If $p_b$ is a tree vertex or the last vertex before $p_b$ on a $p_a$–$p_b$ path is a tree vertex, that vertex has a second leaf $c$ below it with $\gamma(a)\subsetneq\gamma(c)$, violating (ii); condition (iii) singles out the reticulation $p_b$ as the unique vertex that only reaches $b$. These tests use only reachability, so they apply to arbitrary binary networks and need no class assumption.

## Sources

- P. L. Erdős, C. Semple and M. Steel, *A class of phylogenetic networks reconstructable from ancestral profiles*, arXiv:1901.04064 (2019). <https://doi.org/10.48550/arXiv.1901.04064> Lemma 3.1, Corollary 3.2 and Lemma 3.3 (Section 3).
