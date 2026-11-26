# Orchard networks are reconstructible from ancestral profiles

**Setting.** Binary rooted phylogenetic networks on $X$, cherries and reticulated cherries are as in the companion article. *Reducing* a cherry $\{a,b\}$ deletes $b$; *cutting* a reticulated cherry with reticulation leaf $b$ deletes the arc $(p_a,p_b)$; in both cases degree-$2$ vertices are suppressed. A sequence of such operations is *complete* if it ends with a single vertex, and $N$ is an *orchard network* if it admits a complete sequence. Label the non-leaf vertices $v_1,\dots,v_t$. The *ancestral tuple* of $x\in X$ is $\sigma(x)\in\mathbb Z_{\ge 0}^t$ whose $i$-th entry is the number of directed paths from $v_i$ to $x$, and the *ancestral profile* is $\Sigma_N=\{(x,\sigma(x)) : x\in X\}$. A network $N'$ on $X$ *realises* $\Sigma_N$ if, for some labelling of its non-leaf vertices, $\Sigma_{N'}=\Sigma_N$.

**Theorem.**

1. In an orchard network every maximal sequence of cherry reductions and reticulated-cherry cuts is complete, and each such operation maps an orchard network to an orchard network; hence orchard membership can be tested in polynomial time.
2. If $N$ is an orchard network on $X$ with vertex set $V$, then up to isomorphism $N$ is the unique phylogenetic network on $X$ (orchard or not) realising $\Sigma_N$, and $N$ can be reconstructed from $\Sigma_N$ in time

$$ O\bigl(|X|^3\,|V|^3\bigr) . $$

3. Tree-child networks and tree-sibling time-consistent networks are orchard. In particular, a tree-child network is determined among tree-child networks by the multiset of its path tuples $\pi(v)=(\#\text{paths } v\to x_1,\dots,\#\text{paths } v\to x_n)$, recovering the earlier encoding results for these classes; orchard networks, unlike tree-child networks (at most $|X|-1$ reticulations) and tree-sibling time-consistent networks (at most $2|X|-4$), can have arbitrarily many reticulations.

## Depends on

- [Ancestral sets detect cherries and reticulated cherries](ancestral-sets-detect-cherries-and-reticulated-cherries.md)

## Expansion

The ancestral sets $\gamma(x)$ (the supports of the tuples $\sigma(x)$) identify a cherry or reticulated cherry of any network realising $\Sigma_N$, together with which leaf is the reticulation leaf. Deleting $b$, or cutting the reticulated cherry, transforms the profile in a way that only depends on $\Sigma_N$, and the new profile is that of the reduced network. Because $N$ is orchard, the reduced network is orchard, so induction on $|X|$ plus the number of reticulations shows it is the unique realiser; putting the pair back is forced, so every realiser of $\Sigma_N$ is isomorphic to $N$. Ancestral sets alone are weaker than ancestral tuples: the paper gives two non-isomorphic orchard networks with identical ancestral sets. Uniqueness also fails for tree-based networks in general.

## Sources

- P. L. Erdős, C. Semple and M. Steel, *A class of phylogenetic networks reconstructable from ancestral profiles*, arXiv:1901.04064 (2019). <https://doi.org/10.48550/arXiv.1901.04064> Lemma 2.1, Theorems 2.2 and 2.3 (Section 2), Proposition 4.1 and Corollary 4.2 (Section 4), Lemma 5.1 and the algorithm of Section 5.
