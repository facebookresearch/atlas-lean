# MaxGAC is D^P-complete

Recognising the largest generalized arc consistent subdomain is complete for the class $D^P$ of intersections of an NP language with a coNP language, already for constraints given by binary relations on six colours; it is therefore not in NP unless NP $=$ coNP.

A language $L$ is in $D^P$ when $L=L_1\cap L_2$ for some $L_1$ in NP and some $L_2$ in coNP. Let MaxGAC be the problem of the [decision problems of generalized arc consistency](gac-reasoning-problems.md): given an encoded constraint $C$, an initial domain $D_0$ and $D\subseteq D_0$, decide whether $D$ is the GAC closure of $D_0$. Let $\mathcal C_6$ be the type whose instances are encoded by a number $n\ge1$ of variables and a binary relation on $V_6=\{r_1,g_1,b_1,r_2,g_2,b_2\}$ for each pair of distinct variables, a tuple being allowed when every pair of its entries lies in the corresponding relation.

1. For every constraint type $\mathcal C$ with a uniform polynomial-time evaluator and a set of valid encodings decidable in polynomial time, MaxGAC($\mathcal C$) is in $D^P$. ($\mathcal C_6$ below has such encodings.)
2. MaxGAC($\mathcal C_6$) is $D^P$-complete under polynomial-time many-one reductions.

## Depends on

- [Decision problems of generalized arc consistency](gac-reasoning-problems.md): the problem MaxGAC and the encoding model.
- [The complexity class NP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/np.md): the first factor in the definition of $D^P$.
- [The class coNP](../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md): the second factor in the definition of $D^P$.
- [Polynomial-time many-one reduction](../../../TheoryOfComputation/np-completeness/cook-levin/binary-encoding-of-cnf-formulas/poly-many-one-red.md): the reductions in the completeness claim.

## Proof depends on

- [Generalized arc consistency](generalized-arc-consistency.md): the GAC closure of $D_0$ is the set of values of $D_0$ that have a support in $D_0$; used for membership.
- [3-COLOR is NP-complete](../../../TheoryOfComputation/np-completeness/graph-coloring-and-partitioning/graph-3-coloring/part-09/col3-dec-np-complete.md): graph 3-colourability is NP-complete, so its complement is coNP-complete; the source reduces from 3-colourability and non-3-colourability.

## Expansion

*Membership.* Since the GAC closure of $D_0$ consists of the values of $D_0$ supported in $D_0$, $D$ equals the closure iff (a) $C$ is GAC on $D$ and (b) no value of $D_0$ outside $D$ has a support in $D_0$. Indeed, (a) makes $D$ a GAC subdomain, hence $D$ is contained in the closure, and (b) says the closure has no value outside $D$. With valid encodings recognized in polynomial time, condition (a) together with validity is in NP (one support per value of $D$) and condition (b) together with validity is in coNP (a single support of an outside value refutes it), so MaxGAC is their intersection. Condition (b) alone does not suffice: for a unary constraint allowing only $a$, with $D=D_0=\{a,b\}$, (b) holds vacuously but $D$ is not GAC, since $b$ has no support.

*Hardness.* Let $L$ be in $D^P$, $L=L_1\cap L_2$ with $L_1$ in NP and $L_2$ in coNP. Since 3-COLOR is NP-complete, there are polynomial-time many-one reductions $f$ from $L_1$ to 3-COLOR and $g$ from the complement of $L_2$ (in NP) to 3-COLOR, so $x\in L$ iff $f(x)$ is accepted by 3-COLOR and $g(x)$ is not. Turn each of the two strings into a graph: a string that 3-COLOR rejects for failing to decode, or for an edge endpoint out of range, becomes $K_4$, which is not 3-colourable, so the acceptance of 3-COLOR and of its complement is unchanged; a valid string becomes its graph, symmetrized with loops dropped as in 3-COLOR (a valid empty graph is 3-colourable). Pad both graphs with isolated vertices to a common vertex set of size $\max(1,n_1,n_2)$, which preserves 3-colourability. Then $x\in L$ iff the first graph is 3-colourable and the second is not. Give every vertex the domain $V_6$. For a pair of vertices adjacent in both graphs allow pairs of different colours with the same subscript; adjacent only in graph 1, allow different pairs with subscript 1 and all pairs with subscript 2; symmetrically for graph 2 only; adjacent in neither, allow every pair with equal subscripts. The subscript is then constant on any allowed tuple, and the allowed tuples with subscript $i$ are the proper 3-colourings of graph $i$. With $D_0$ the full domains and $D(x)=\{r_1,g_1,b_1\}$ for every vertex, $C$ is GAC on $D$ iff graph 1 is 3-colourable (colour symmetry), and some value with subscript 2 is supported in $D_0$ iff graph 2 is 3-colourable. So MaxGAC$[C,D_0,D]$ holds iff graph 1 is 3-colourable and graph 2 is not.

If MaxGAC($\mathcal C_6$) were in NP then every $D^P$ language, in particular the coNP-complete complement of 3-colourability, would be in NP, giving NP $=$ coNP.

The source states the theorem as "MaxGAC is $D^P$-complete" over constraints given by polynomial-time tests and proves hardness with this six-value construction; the membership argument is the standard check of the two halves of the definition.

## Sources

- C. Bessiere, E. Hebrard, B. Hnich and T. Walsh, "The complexity of reasoning with global constraints", *Constraints* 12(2) (2007), 239–259, doi:10.1007/s10601-006-9007-3. Definition of $D^P$ in §2; Theorem 1 (MaxGAC is $D^P$-complete) and its proof in §3.3 of arXiv:0903.1139v1, [https://arxiv.org/abs/0903.1139v1](https://arxiv.org/abs/0903.1139v1).
- C. H. Papadimitriou and M. Yannakakis, "The complexity of facets (and some facets of complexity)", *Journal of Computer and System Sciences* 28(2) (1984), 244–259, doi:10.1016/0022-0000(84)90068-0. Introduction of $D^P$, cited by the source for the class.
