# Segmentation process for discrete-time single-crossover recombination

Sites are $S = \{0,1,\dots,n\}$, each site $i$ carries a letter from a finite set $X_i$, and types are sequences $x = (x_0,\dots,x_n) \in X = X_0 \times \dots \times X_n$. The links between neighbouring sites form $L = \{\tfrac12, \tfrac32, \dots, \tfrac{2n-1}{2}\}$, link $\alpha = \tfrac{2i+1}{2}$ lying between sites $i$ and $i+1$. For a population, i.e. a non-negative measure $\omega$ on $X$, let $\pi_{<\alpha}.\omega$ and $\pi_{>\alpha}.\omega$ be its marginals on the sites before and after $\alpha$. The **recombinator** at $\alpha$ is

$$R_\alpha(\omega) = \frac{1}{\|\omega\|}\, (\pi_{<\alpha}.\omega) \otimes (\pi_{>\alpha}.\omega),$$

the population obtained when every individual is cut at $\alpha$ and leading and trailing segments are relinked at random. Recombinators are idempotent and commute, so the composite recombinators $R_G = \prod_{\alpha\in G} R_\alpha$, $G \subseteq L$ (with $R_\varnothing$ the identity), satisfy $R_G R_H = R_{G\cup H}$. (For probability measures the normalising factor is $1$.)

**Wright–Fisher model with single-crossover recombination.** Each link has a crossover probability $\varrho_\alpha > 0$, with $\sum_{\alpha} \varrho_\alpha \le 1$. In each generation of $N$ individuals, every offspring independently either (with probability $\varrho_\alpha$) is the recombinant at link $\alpha$ of two parents chosen uniformly with replacement, taking the sites up to $\alpha$ from the first and those after $\alpha$ from the second, or (with probability $1 - \sum_\alpha \varrho_\alpha$) copies a single uniformly chosen parent. Let $\widehat Z^{(N)}_t$ be the type frequencies in generation $t$.

**Proposition (infinite-population limit; Baake–von Wangenheim, Section 2.2).** If $\widehat Z^{(N)}_0 \to p_0$, then for each fixed $t \in \mathbb N_0$, $\widehat Z^{(N)}_t \to p_t$ in mean square, where

$$p_t = \Phi(p_{t-1}), \qquad \Phi(p) = \Big(1 - \sum_{\alpha\in L}\varrho_\alpha\Big)\, p + \sum_{\alpha\in L} \varrho_\alpha\, R_\alpha(p).$$

The solution has the form $p_t = \sum_{G\subseteq L} a_G(t)\, R_G(p_0)$ with $a_G(0) = \delta_{G,\varnothing}$, non-negative coefficients summing to $1$.

**Segmentation process.** For $G \subseteq L$ let $\mathcal L_G$ be the ordered partition of $L\setminus G$ into its maximal runs of consecutive links (the segments left after cutting at every link of $G$). The segmentation process is the Markov chain $(F_\tau)_{\tau\ge0}$ on subsets of $L$ with $F_0 = \varnothing$: given $F_\tau = G$, independently in every segment $I \in \mathcal L_G$ either no link is chosen (probability $1 - \sum_{\alpha\in I}\varrho_\alpha$) or exactly one link $\alpha \in I$ is chosen (probability $\varrho_\alpha$), and $F_{\tau+1}$ is $G$ together with the chosen links.

**Theorem (Baake–von Wangenheim, Section 3.3).** For all $G \subseteq L$ and $\tau \ge 0$,

$$P(F_\tau = G) = a_G(\tau).$$

**Theorem (type distribution via the ancestral process; Section 3.2).** If $\widehat Z^{(N)}_0 \to p_0$, then for each fixed $t$ the type of any given individual converges in law to $\sum_{G} P(F_t = G)\, R_G(p_0)$, and

$$\lim_{N\to\infty} \widehat Z^{(N)}_t = \sum_{G\subseteq L} P(F_t = G)\, R_G(p_0) \quad \text{in mean square}.$$

Unlike continuous time, links are not independent here: a segment receives at most one crossover per generation, so the coefficients do not factorize over links.

## Depends on

- [Random mating with recombination](../recombine.md)

## Expansion

Trace the ancestry of the sites of one individual backwards. Each generation, the current ancestral segments split at a link chosen with the crossover probabilities, and pieces sitting in different individuals coalesce only with probability $O(1/N)$: the probability of no coalescence up to time $t$ is at least $1 - n(n+1)t/(2N) + O(1/N^2)$ (Lemma in Section 3.1). In the limit the partition of sites into ancestral pieces is an ordered partition refined exactly as the segmentation process prescribes, and the pieces come from independent draws from $p_0$, which is what $R_{F_t}(p_0)$ encodes. Comparing with the forward law of large numbers, and using that the $R_G(p_0)$ are generically affinely independent, identifies $a_G(\tau)$ with $P(F_\tau = G)$; a second proof checks that both satisfy the same recursion.

## Sources

- E. Baake and U. von Wangenheim, *Single-crossover recombination and ancestral recombination trees*, *Journal of Mathematical Biology* 68 (2014), 1371–1402, <https://doi.org/10.1007/s00285-013-0662-x>; preprint arXiv:1206.0950, <https://doi.org/10.48550/arXiv.1206.0950>.
