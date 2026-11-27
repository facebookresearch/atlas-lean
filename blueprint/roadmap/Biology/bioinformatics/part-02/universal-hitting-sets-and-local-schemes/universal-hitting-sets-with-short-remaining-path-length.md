# Universal hitting sets with short remaining path length

Let $\Sigma = \{0, \dots, \sigma - 1\}$, $\sigma \ge 2$. A set $A \subseteq \Sigma^k$ **hits** a string if one of its $k$-mers occurs in it, and is a **universal hitting set (UHS)** for length $L$ if it hits every string of length $L$. In the de Bruijn graph $B_{\Sigma,k}$ (vertices $\Sigma^k$, an edge for each $(k+1)$-mer), $A$ is an **$(\alpha, l)$-UHS** if its **relative size** is $\alpha = |A|/\sigma^k$ and it meets every walk of $l$ vertices; $l$ bounds the **remaining path length** of $B_{\Sigma,k} \setminus A$.

A **local (selection) scheme** with window $w$ is a function $f : \Sigma^w \to \{0, \dots, w-1\}$ selecting position $i + f(S[i, w])$ in every window of a string $S$; it is **forward** if consecutive selections never move backwards ($f(\omega_2) \ge f(\omega_1) - 1$). Its **density** is the expected fraction of selected positions on an infinite i.i.d. uniform string, always in $[1/w, 1]$.

**Contexts.** Window $S[i, w]$ selects a new position iff its selection differs from those of the previous $w - 1$ windows, which is determined by the $(2w-1)$-mer context ending with that window. With $S_f \subseteq \Sigma^{2w-1}$ the contexts that select a new position, the density of $f$ equals $|S_f| / \sigma^{2w-1}$ (equivalently the particular density on a de Bruijn sequence of order at least $2w - 1$).

**Theorem (schemes give UHS).** If $f$ is a local scheme of density $d$, then $S_f$ is a $(d, w)$-UHS over $(2w-1)$-mers; if $f$ is forward, the analogous set of $(w+1)$-mer contexts is a $(d, w)$-UHS.

**Theorem (forbidden-word UHS).** There is an explicit set $\mathcal F_{\sigma,w} \subseteq \Sigma^w$, defined from a run $0^{d}$ of zeros with $d$ of order $\log_\sigma w$, that is an $(O(\ln w / w), w)$-UHS, giving a selection scheme within a $\ln w$ factor of the $\Omega(1/w)$ lower bound.

**Theorem (Mykkeltveit sets).** The Mykkeltveit decycling set $\mathcal M_{\sigma,w}$, which contains exactly one $w$-mer from each pure rotation cycle (a necklace count $N_{\sigma,w} = \frac1w\sum_{d \mid w}\varphi(d)\sigma^{w/d}$), leaves remaining paths of length polynomial in $w$: the remaining path length $g(w)$ satisfies $\Omega(w^2) \le g(w) \le O(w^3)$, the upper bound via a geometric relaxation and the lower bound by an explicit path.

## Depends on

- [De Bruijn multigraph of a string](../../de-bruijn-graph-genome-assembly/de-bruijn-edges.md)

## Expansion

Every $w$ consecutive windows must select at least one new position, so among any $w$ consecutive contexts one lies in $S_f$, which is the hitting property; for forward schemes one look-back window suffices. Any UHS hits all infinite strings, so it is a decycling set and must meet each of the $N_{\sigma,w} = \Theta(\sigma^w/w)$ rotation cycles, giving relative size $\Omega(1/w)$. The forbidden-word count reduces to the probability that a finite-state automaton recognizing $0^d$ has not accepted after $w$ random letters, controlled by the dominant eigenvalue of its $d \times d$ substochastic matrix, so that clause dominates and the size is $O(\ln w / w)$. For Mykkeltveit sets, embedding each $w$-mer as a weighted centre of mass of the $w$-th roots of unity turns paths avoiding the set into trajectories that drift monotonically in the upper half-plane under rotations, bounding their length although $\sim(1 - 1/w)\sigma^w$ vertices remain.

## Sources

- H. Zheng, C. Kingsford, G. Marçais, "Lower density selection schemes via small universal hitting sets with short remaining path length", Journal of Computational Biology 28(4) (2021) 395–409, Sections 2.1–2.2 (main results) and 3.1–3.4 (contexts, forbidden-word set, Mykkeltveit embedding and path bounds), <https://doi.org/10.1089/cmb.2020.0432>, PMCID PMC8066347.
