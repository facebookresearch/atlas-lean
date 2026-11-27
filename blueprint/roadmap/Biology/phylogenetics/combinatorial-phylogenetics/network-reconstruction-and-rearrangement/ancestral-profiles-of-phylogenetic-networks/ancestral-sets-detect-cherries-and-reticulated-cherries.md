# Ancestral sets detect cherries and reticulated cherries

**Setting.** A (rooted) phylogenetic network on $X$ is an acyclic digraph without parallel arcs, with a root of in-degree $0$ and out-degree $2$, leaves of in-degree $1$ and out-degree $0$ forming the set $X$, and all other vertices either tree vertices (in-degree $1$, out-degree $2$) or reticulations (in-degree at least $2$, out-degree $1$); it is binary when every reticulation has in-degree $2$. For $x\in X$ with parent $p_x$, the *ancestral set* is

$$
\gamma(x)=\{v\in V\setminus X : x \text{ is reachable from } v\} .
$$

A $2$-element set $\{a,b\}\subseteq X$ is a *cherry* if $p_a=p_b$, and a *reticulated cherry with reticulation leaf $b$* if $p_b$ is a reticulation and $(p_a,p_b)$ is an arc. The *grandparents* of $b$ are the parents of $p_b$.

**Lemma.** Let $N$ be a phylogenetic network on $X$ and $a\ne b$ in $X$.

1. If $N$ is binary, $\gamma(a)\subseteq\gamma(b)$ if and only if $b$ is reachable from $p_a$.
2. If $N$ is binary, $\{a,b\}$ is a cherry if and only if $\gamma(a)=\gamma(b)$.
3. $\{a,b\}$ is a reticulated cherry with reticulation leaf $b$ **and all grandparents of $b$ are tree vertices** if and only if (i) $\gamma(a)\subsetneq\gamma(b)$, (ii) there is no $x\in X\setminus\{b\}$ with $\gamma(a)\subsetneq\gamma(x)$, and (iii) exactly one vertex lies in $\gamma(b)$ but in no $\gamma(x)$ with $x\in X\setminus\{b\}$.

The condition on the grandparents in part 3 cannot be dropped: Bai, Erdős, Semple and Steel show with the binary orchard network $N$ of their Fig. 2, taking $a=x_3$ and $b=x_4$, that the equivalence fails without it; that network contains a stack (a reticulation that is a parent of another reticulation).

## Expansion

Since $a$ has the single parent $p_a$, $\gamma(a)$ is $p_a$ together with its ancestors, so $\gamma(a)\subseteq\gamma(b)$ exactly when $p_a\in\gamma(b)$; acyclicity then gives part 2. For part 3, conditions (i) and (ii) place $p_a$ immediately above the parent of $b$ among the ancestors of leaves, and condition (iii) singles out the reticulation $p_b$ as the unique vertex that reaches only $b$. The proof of the corrected lemma follows the argument of the original Lemma 3.3, using the grandparent condition where that argument needs every other parent of $p_b$ to have a second child.

## Sources

- P. L. Erdős, C. Semple and M. Steel, *A class of phylogenetic networks reconstructable from ancestral profiles*, Mathematical Biosciences 313 (2019) 33–40. <https://doi.org/10.1016/j.mbs.2019.04.009> Lemma 3.1 and Corollary 3.2 (parts 1 and 2, proved there for binary networks). Its Lemma 3.3 omits the grandparent condition and is false as stated.
- A. Bai, P. L. Erdős, C. Semple and M. Steel, *Defining phylogenetic networks using ancestral profiles*, Mathematical Biosciences 332 (2021) 108537. <https://doi.org/10.1016/j.mbs.2021.108537> Lemma 5.1 of the Appendix (part 3, corrected) and Fig. 2 (the counterexample to the uncorrected form).
