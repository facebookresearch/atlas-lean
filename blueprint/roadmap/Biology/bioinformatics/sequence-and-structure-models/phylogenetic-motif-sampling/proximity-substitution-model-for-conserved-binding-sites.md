# Proximity substitution model for conserved binding sites

**Model.** Let $w = (w_{\alpha i})$ be a weight matrix of width $\ell$ over the alphabet $\{A, C, G, T\}$, with $w_{\cdot i}$ a probability vector for each position $i$. A binding site evolves along a branch of duration $t$ with mutations at rate $\gamma$ per position, and a mutation at position $i$ is fixed toward base $\alpha$ with probability proportional to $w_{\alpha i}$. With **proximity** $q = e^{-\gamma t} \in (0,1]$, the probability that position $i$ carries base $\alpha$ at the end of the branch given base $\beta$ at its start is

$$T_i(\alpha \mid \beta; q) = q\, \mathbf{1}\{\alpha = \beta\} + (1 - q)\, w_{\alpha i} .$$

**Proposition.**

1. *(Composition.)* $\sum_{\gamma'} T_i(\alpha \mid \gamma'; q_2)\, T_i(\gamma' \mid \beta; q_1) = T_i(\alpha \mid \beta; q_1 q_2)$, so inserting an intermediate ancestor multiplies proximities.
2. *(Stationarity.)* $\sum_\beta T_i(\alpha \mid \beta; q)\, w_{\beta i} = w_{\alpha i}$; as $q \to 0$, $T_i(\alpha \mid \beta; q) \to w_{\alpha i}$, the law of an independently sampled site.
3. *(Star phylogeny.)* If an aligned window contains bases $s_1, \dots, s_N$ at position $i$ in $N$ orthologous sequences descending independently from a common ancestor with proximities $q_1, \dots, q_N$, and the ancestral base is drawn from $w_{\cdot i}$, then

$$P(W_i \mid w) = \sum_{\alpha} w_{\alpha i} \prod_{j = 1}^{N} \big(q_j \mathbf{1}\{s_j = \alpha\} + (1 - q_j)\, w_{s_j i}\big), \qquad P(W \mid w) = \prod_{i = 1}^{\ell} P(W_i \mid w),$$

and for a general tree $P(W_i \mid w)$ is obtained by Felsenstein pruning with the transition matrices $T_i$.

The background probability of a window is the same expression with $w_{\alpha i}$ replaced by background base frequencies.

## Depends on

- [Felsenstein's pruning recursion](../../../phylogenetics/felsenstein-s-pruning-algorithm/prune.md)

## Expansion

With probability $q$ no mutation occurs and the base is kept; otherwise at least one mutation occurs and the last fixed base is distributed as $w_{\cdot i}$, independent of the start, giving $T_i$. Composition follows from $\big(qI + (1-q)\mathbf{w}\mathbf{1}^\top\big)$-type algebra: the product of two such matrices keeps the base with probability $q_1 q_2$ and otherwise draws from $w_{\cdot i}$, because $w_{\cdot i}$ is invariant under each factor (item 2). Item 3 sums over the unobserved ancestral base, using conditional independence of the descendants given the ancestor. Conservation of a column then counts as evidence for a binding site only beyond what proximity alone explains: when $q$ is large, aligned identical bases are likely under the background too. In PhyloGibbs these window probabilities enter a posterior over configurations of colored windows that is sampled by Gibbs moves and simulated annealing.

## Sources

- R. Siddharthan, E. D. Siggia and E. van Nimwegen, *PhyloGibbs: a Gibbs sampling motif finder that incorporates phylogeny*, PLoS Computational Biology (2005). <https://doi.org/10.1371/journal.pcbi.0010067> (PMCID: PMC1309704). Results: "Incorporating Phylogeny"; Materials and Methods: derivation of $P(S_c)$ and the evolutionary model for aligned windows.
