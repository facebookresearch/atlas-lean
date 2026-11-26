# Bounded reversal and prefix-reversal distance as permutation classes

**Setting.** A genome of $n$ ordered genes is modelled by a permutation $\pi\in S_n$. A *reversal* reverses a segment of consecutive entries of $\pi$; a *prefix reversal* reverses an initial segment. The reversal distance $rd(\pi)$ (resp. prefix-reversal distance $prd(\pi)$) is the minimum number of such operations sorting $\pi$ to the identity. Let $B_k^{(rd)}$ (resp. $B_k^{(prd)}$) be the set of permutations of any length with distance at most $k$.

A permutation $\sigma$ is a *pattern* of $\tau$ if some subsequence of $\tau$ is order-isomorphic to $\sigma$. A *peg permutation* $\pi^\varepsilon$ decorates each entry with $+$, $-$ or $\bullet$; its *grid class* $\mathrm{Grid}(\pi^\varepsilon)$ is the set of permutations obtained by replacing each $+$ entry with an increasing run of any length $\ge0$, each $-$ entry with a decreasing run of any length $\ge0$, and each $\bullet$ entry with either nothing or a single entry, then rescaling. A peg permutation is *clean compact* if it has no strip (maximal run of consecutive values $j,j+1,\dots$ decorated $+$/$\bullet$, or $j,j-1,\dots$ decorated $-$/$\bullet$) of length $\ge2$.

**Theorem (pattern closure).** $B_k^{(rd)}$ is a down-set of the pattern order, i.e. a permutation class; so is $B_k^{(prd)}$.

**Theorem (generating permutations, reversals).** For every $k\ge1$ there are finitely many clean compact peg permutations $\alpha_{(1)},\dots,\alpha_{(N)}$, each of length $2k+1$, without $\bullet$ decorations and at reversal distance exactly $k$, such that

$$B_k^{(rd)}=\bigcup_{j=1}^{N}\mathrm{Grid}\big(\alpha_{(j)}\big),$$

and they are exactly the maximal clean compact peg permutations of distance at most $k$.

**Theorem (basis length, reversals).** Every element of the clean compact peg basis of the decorated ball $\hat B_k^{(rd)}$ has length at most $2k+1$; in particular this basis is finite. For $k=1$ it is $\{1^-2^-,\ 2^+1^\bullet,\ 2^\bullet1^+\}$.

**Theorem (prefix reversals).** The generating set of $B_k^{(prd)}$ (its maximal clean compact peg permutations) has exactly $k!$ elements, and every clean compact peg basis permutation of $\hat B_k^{(prd)}$ has length at most $k+2$; length $k+2$ occurs only for four explicit exceptional families $\Theta_e,\Lambda_e$ ($k+2$ even) and $\Theta_o,\Lambda_o$ ($k+2$ odd).

## Expansion

If $\tau$ is sorted by $k$ reversals, deleting entries maps each reversal to a (possibly trivial) reversal of the pattern, giving pattern closure. Every sorting sequence for a peg permutation also sorts every monotone inflation, because a strip moves as a block; this is why the ball is a union of grid classes. A single reversal acting on $\mathrm{Grid}(\pi^\varepsilon)$ cuts at most two places, so the grid classes reached in one more step come from inserting two new strips, which raises the generator length by $2$ per step and gives length $2k+1$. For prefix reversals only one cut is made per step, giving the recursive construction that multiplies the number of generators by $k+1$ at step $k+1$, hence $k!$.

## Sources

- Giulio Cerbai, Luca Ferrari, "Permutation patterns in genome rearrangement problems: the reversal model", arXiv:1903.08774: Proposition 2.1 (down-set), Theorem 2.7 and Corollary 2.9 (generating permutations), Theorem 2.12, Corollary 2.13 and Proposition 2.14 (basis bounds), Proposition 3.1 and Theorems 3.2–3.3 (prefix generating set of size $k!$), Theorems 3.5, 3.8–3.9 (prefix basis bounds and exceptional permutations). <https://doi.org/10.48550/arXiv.1903.08774> Published version: Discrete Applied Mathematics 279 (2020) 34–48, <https://doi.org/10.1016/j.dam.2019.10.012>.
