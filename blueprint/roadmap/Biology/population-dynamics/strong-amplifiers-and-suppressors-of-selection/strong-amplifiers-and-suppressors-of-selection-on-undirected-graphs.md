# Strong amplifiers and suppressors of selection on undirected graphs

Consider the Moran process of Lieberman, Hauert and Nowak on a connected undirected graph $G$ with $n$ vertices: mutants have fitness $r$, non-mutants fitness $1$, a vertex is chosen to reproduce with probability proportional to fitness, and its offspring replaces a uniformly random neighbour. Starting from a single mutant at a uniformly random vertex, let $\rho_G(r)$ be the fixation probability (on the complete graph, $\rho_G(r)\to1-1/r$). A family is a *strong amplifier* if $\rho_G(r)\to1$ and a *strong suppressor* if $\rho_G(r)\to0$ as $n\to\infty$. Both were known to exist for directed graphs; for undirected graphs the prevailing belief was that neither does.

**Theorem.**

1. (Strong amplifiers.) There is a family of undirected graphs $A_{n,\epsilon}$, $n\ge1$, $0<\epsilon\le1$, with $\Theta(n)$ vertices, such that for all $r\ge1+\epsilon$

$$\rho_{A_{n,\epsilon}}(r) = 1-O\!\left(\frac{\log n}{\epsilon\, n^{1/3}}\right).$$

2. (Near-optimality.) For every undirected graph $G$ on $n$ vertices and every $r>1$,

$$\rho_G(r) = 1-\Omega\!\left(\frac{1}{r^{5/3}\, n^{1/3}\log^{4/3} n}\right),$$

and more crudely $\rho_G(r)\le1-1/(5\sqrt{r^3 n})$.

3. (Strong suppressors.) There is a family of undirected graphs $B_n$ with $\Theta(n)$ vertices such that

$$\rho_{B_n}(r) = O\!\left(\frac{r^2\log n}{n^{1/4}}\right).$$

**Harmonic-volume bound.** For a vertex set $S$ let $\mathrm{hvol}(S)=\sum_{u\in S}1/\deg(u)$ (the "temperature" of $S$). If $G$ has minimum degree $\delta$ and the initial mutant set is $S$, then

$$\rho^S_G(r)\ \ge\ \frac{1-r^{-\delta\,\mathrm{hvol}(S)}}{1-r^{-\delta\,\mathrm{hvol}(V)}},$$

so in particular $\rho^S_G(r)\ge1-n^{-c}$ as soon as $\mathrm{hvol}(S)\ge c\,\delta^{-1}\log_r n$.

## Expansion

1. The harmonic-volume bound comes from a supermartingale: in each step $r^{-\delta\,\mathrm{hvol}(S_t)}$ does not increase in expectation, because a mutant at $u$ invades a neighbour of degree $d$ at rate proportional to $r/\deg(u)$ while being invaded at rate proportional to $1/\deg(u)$ per neighbour; optional stopping gives the bound.
2. Amplifier $A_{n,\epsilon}$: most vertices are low-degree leaves attached to hubs; a mutant on a leaf is rarely overwritten, and once it reaches a hub the harmonic volume of the mutant set grows past $\delta^{-1}\log_r n$, after which fixation is almost sure.
3. Suppressor $B_n$: almost all vertices sit in regions that are frequently overwritten from high-degree vertices, so a mutant usually dies before spreading, while the rare favourable starts carry total probability $O(r^2 n^{-1/4}\log n)$.
4. The upper bound in item 2 shows the amplifier exponent $1/3$ cannot be improved beyond logarithmic factors.

## Depends on

- [Optimal extinction probability of amplifiers of selection in the Moran process](optimal-extinction-probability-of-amplifiers-of-selection.md)

## Sources

- G. Giakkoupis, *Amplifiers and suppressors of selection for the Moran process on undirected graphs*, arXiv:1611.01585 (Theorems 1, 2, 3, Lemma 6, Corollary 7 and Corollary 14). <https://doi.org/10.48550/arXiv.1611.01585>
