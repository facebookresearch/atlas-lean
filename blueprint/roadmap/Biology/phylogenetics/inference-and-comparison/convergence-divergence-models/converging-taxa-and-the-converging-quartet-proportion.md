# Converging taxa and the converging-quartet proportion

**Model.** A convergence-divergence model (CDM) $\mathcal{N} = (T, \boldsymbol{\Pi}, \mathfrak{E}, \mathfrak{Q}, \mathfrak{t})$ consists of a principal tree $T$ (binary, rooted, leaf-labelled, ultrametric, positive edge lengths), a root distribution $\boldsymbol{\Pi}$, and a sequence of epochs from root to tips. Each epoch $E_i$ carries a partition of the current lineages into convergence-divergence groups, a rate matrix $\boldsymbol{Q}_i$ and a duration $\tau_i$. A set of taxa is *converging* in an epoch when, under the continuous-time Markov model, the probability that all of them are in identical states increases with time while every other state combination decreases. In the 2-state general CDM, group $C_r$ jumps from all-0 to all-1 at rate $\alpha_r$ and back at rate $\beta_r$, with $\alpha_r/\beta_r$ common to all groups and $\boldsymbol{\Pi}$ stationary.

**Standing assumptions (Section 3.2).** The Proposition, its consequences and the consistency statement below assume: (1) the generating CDM is a 2-state general CDM; (2) the principal tree is rooted by a single outgroup taxon $o$; (3) no convergence group contains $o$; (4) no event is both a speciation event and a convergence-divergence event; (5) each epoch has at most one convergence group; (6) every convergence group is a partition into exactly two subsets; (7) each convergence group appears in at most one epoch; (8) no two consecutive epochs both have convergence groups; (9) no convergence group is nested in another, where $C_2$ is nested in $C_1$ if $C_1$ is before $C_2$ and on some displayed CDM their restrictions belong to identical decorated partitions; (10) there are no sister convergence groups; (11) the generating parameter is a generic point of the parameter space of the generating CDM. The consistency statement assumes in addition that the sites are independent and identically distributed draws from the generating CDM (Theorem 7). The limit theorem uses only (1) and (11).

**Theorem (limit of converging taxa).** If $a, b$ lie in the same convergence group $C_i$ of an epoch, then as the tip-epoch length $t \to \infty$ the character states of $a$ and $b$ become identical.

**Proposition (converging quartets).** Let $C = \{c_1, c_2\}$ be a convergence group, $a \in c_1$, $b \in c_2$, $v$ the most recent common ancestor of $a$ and $b$ on $T$, $X_v$ the leaves below $v$, $X_C = c_1 \cup c_2$, and $N$ the number of taxa. Among the $N-3$ quartets containing $a$, $b$ and the outgroup, the expected proportion displaying convergence of $\{a,b\}$ is

$$\frac{|X_v \setminus X_C|}{N-3} = \frac{|X_v| - |X_C|}{N-3}.$$

In particular, a sister convergence group has expected proportion $0$, and, by (9), distinct convergence groups share no pair of converging taxa (nested groups would share one), so all convergence groups are identifiable from the displayed 4-taxon CDMs once sister groups are suppressed.

**Consistency.** Inferring the principal tree by BIC model selection on 4-taxon CDMs and assembling them with the rooted-triple metrization, in which $d_{\mathcal{T}}(x,y) = 2|R_{x,y}| + 2$ for distinct non-outgroup taxa ($R_{x,y}$ the displayed rooted quartets in which $x$ and $y$ are non-sisters), is statistically consistent provided the largest convergence parameter is below some constant $c > 0$.

## Expansion

Within a convergence group the joint process has absorbing-like attraction to the diagonal states, so the off-diagonal mass decays exponentially and the members become identical in the long-epoch limit. A quartet $\{o, a, b, x\}$ reveals convergence of $a$ and $b$ only if $x$ separates them on the principal tree, i.e. $x$ descends from $v$ but is not itself part of the converging group, which counts $|X_v| - |X_C|$ of the $N-3$ choices. All 4-taxon CDMs considered are pairwise distinguishable (their parameter spaces differ in dimension or meet in a lower-dimensional set), which makes BIC selection consistent.

## Sources

- J. D. Mitchell, B. R. Holland, "Convergence-divergence models: Generalizations of phylogenetic trees modeling gene flow over time", *Bulletin of Mathematical Biology* 87(12) (2025), 178, Definitions 1-4, Theorem 2, Theorems 5-7, Proposition 9, Corollary 10, Propositions 11-12, <https://doi.org/10.1007/s11538-025-01565-4> (preprint arXiv:2504.07384).
