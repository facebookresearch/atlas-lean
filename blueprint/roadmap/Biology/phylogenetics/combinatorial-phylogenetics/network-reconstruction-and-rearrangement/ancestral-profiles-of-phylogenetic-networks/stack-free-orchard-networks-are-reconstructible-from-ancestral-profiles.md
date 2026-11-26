# Stack-free orchard networks are reconstructible from ancestral profiles

**Setting.** Phylogenetic networks on $X$, cherries and reticulated cherries are as in the companion article (reticulations may have in-degree larger than $2$). *Reducing* a cherry $\{a,b\}$ deletes $b$; *cutting* a reticulated cherry with reticulation leaf $b$ deletes the arc $(p_a,p_b)$; in both cases vertices of in-degree $1$ and out-degree $1$ are suppressed. A sequence of such operations is *maximal* if it ends with a network that has no cherry and no reticulated cherry, and *complete* if it ends with a single vertex; $N$ is an *orchard network* if it admits a complete sequence. A *stack* is an arc $(u,v)$ between two reticulations, and $N$ is *stack-free* if it has none. The *stack identification* $\mathrm{id}(N)$ identifies each class of reticulations joined by stack arcs (the transitive closure of being joined by an arc) to a single vertex and removes the arcs inside the class. Label the non-leaf vertices $v_1,\dots,v_t$. The *ancestral tuple* of $x\in X$ is $\sigma(x)\in\mathbb Z_{\ge 0}^t$ whose $i$-th entry is the number of directed paths from $v_i$ to $x$, and the *ancestral profile* is $\Sigma_N=\{(x,\sigma(x)) : x\in X\}$. A network $N'$ on $X$ *realises* $\Sigma_N$ if, for some labelling of its non-leaf vertices, $\Sigma_{N'}=\Sigma_N$.

**Theorem.**

1. In an orchard network every maximal sequence of cherry reductions and reticulated-cherry cuts is complete, and each such operation maps an orchard network to an orchard network.
2. If $N$ is a **stack-free** orchard network on $X$, then up to isomorphism $N$ is the unique phylogenetic network on $X$ (orchard or not, stack-free or not) realising $\Sigma_N$.
3. If $N$ and $N'$ are orchard networks on $X$ with the same ancestral profile, then $\mathrm{id}(N)\cong\mathrm{id}(N')$.
4. Tree-child networks, and tree-sibling time-consistent networks without stacks, are stack-free orchard networks; a stack-free orchard network on $X$ can have arbitrarily many reticulations, unlike a tree-child network (at most $|X|-1$) or a stack-free tree-sibling time-consistent network (at most $2|X|-4$).

Part 2 fails without the stack-free hypothesis: Fig. 2 of Bai, Erdős, Semple and Steel gives two non-isomorphic binary orchard networks, each containing a stack, with the same ancestral profile. Part 3 is what remains in that case: an ancestral profile of an orchard network determines it only up to stack identification.

## Depends on

- [Ancestral sets detect cherries and reticulated cherries](ancestral-sets-detect-cherries-and-reticulated-cherries.md)

## Expansion

The ancestral sets $\gamma(x)$ (the supports of the tuples $\sigma(x)$) identify a cherry of any network realising $\Sigma_N$, and, when every grandparent of the reticulation leaf is a tree vertex, a reticulated cherry together with its reticulation leaf. In a stack-free orchard network every reticulated cherry has this property, and reducing a cherry or cutting a reticulated cherry keeps a network stack-free and orchard. Deleting $b$, or cutting the reticulated cherry, transforms the profile in a way that depends only on $\Sigma_N$, and the new profile is that of the reduced network; induction on $|X|$ plus the number of reticulations then shows that $N$ is the unique realiser. For part 3, stack identification maps an orchard network to an orchard network and two orchard networks with the same profile to stack-free orchard networks with the same profile, to which part 2 applies.

## Sources

- A. Bai, P. L. Erdős, C. Semple and M. Steel, *Defining phylogenetic networks using ancestral profiles*, Mathematical Biosciences 332 (2021) 108537. <https://doi.org/10.1016/j.mbs.2021.108537> Proposition 2.1 (part 1), Theorem 3.1 (part 2), Theorem 3.2 with Lemma 4.1 (part 3), the discussion after Theorem 3.2 and Fig. 4 (part 4), Fig. 2 (the counterexample without the stack-free hypothesis), and Lemmas 5.2 and 5.3 of the Appendix.
- P. L. Erdős, C. Semple and M. Steel, *A class of phylogenetic networks reconstructable from ancestral profiles*, Mathematical Biosciences 313 (2019) 33–40. <https://doi.org/10.1016/j.mbs.2019.04.009> Corollary 4.2 (the reductions preserve the orchard property). Its Theorem 2.2, which omits the stack-free hypothesis, is false as stated.
