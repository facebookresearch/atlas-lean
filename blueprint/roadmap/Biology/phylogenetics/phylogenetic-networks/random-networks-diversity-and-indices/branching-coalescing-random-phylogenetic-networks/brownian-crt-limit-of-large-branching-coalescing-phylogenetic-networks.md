# Brownian CRT limit of large branching–coalescing phylogenetic networks

**Setting.** Let $\mathscr G$ be the random phylogenetic network generated from one lineage in which lineages branch at rate $1$, die at rate $\alpha$, change to a new color at rate $\mu$, and pairs of lineages of the same color coalesce (hybridize) at rate $2\beta$. View $\mathscr G$ as a rooted metric measure space: the union of lineage segments with the shortest-path metric $d_{\mathscr G}$ and Lebesgue (length) measure $\lambda_{\mathscr G}$; let $\mathscr G_n$ be $\mathscr G$ conditioned to have $n$ colors, and $|\mathscr G_n|=\lambda_{\mathscr G_n}(\mathscr G_n)$ its total branch length. Let $M$ be the number of colors created by one color, and $\zeta>0$ the exponential tilt with $\mathbb E[M\zeta^M]=\mathbb E[\zeta^M]$.

**Theorem.** As $n\to\infty$,

$$\Big(\mathscr G_n,\ r_n,\ \tfrac{C}{\sqrt n}\,d_{\mathscr G_n},\ \tfrac1{|\mathscr G_n|}\lambda_{\mathscr G_n}\Big)\ \xrightarrow{d}\ \mathscr C$$

in the rooted Gromov–Hausdorff–Prokhorov topology, where $\mathscr C$ is Aldous' Brownian continuum random tree and

$$C=\frac{\sqrt{\mathbb E[\zeta^M]\big(\mathbb E[M^2\zeta^M]-\mathbb E[\zeta^M]\big)}}{2\,\mathbb E\big[\sum_{t\in\mathcal M}t\,\zeta^M\big]},$$

with $\mathcal M$ the set of mutation (new-color) times of the founding color. Moreover the uniformly rooted $\mathscr G_n$ has an explicit local weak limit.

## Depends on

- [Offspring law of colors in the branching–coalescing network model](offspring-law-of-colors-in-the-branching-coalescing-network-model.md)

## Expansion

The color tree $\mathscr T$ is a Galton–Watson tree with offspring law $M$; conditioning on $n$ colors is conditioning $\mathscr T$ to have $n$ vertices, and the exponential tilt by $\zeta^M$ makes it critical without changing the conditioned law, while $M$ has exponential moments, so Aldous' theorem gives the CRT limit of $\mathscr T_n$ with scaling $\hat\sigma/(2\sqrt n)$, $\hat\sigma^2$ the variance of the tilted offspring law. Each color's subnetwork has light-tailed diameter, so distances in $\mathscr G_n$ are, to first order, sums along ancestral color paths of the time from a color's root to the mutation creating the next color; a law of large numbers along these paths converts tree distance into network distance at rate $\mathbb E[U^*]$, the mean mutation time in the size-biased color, giving $C$. Hybridization therefore only affects the large-scale geometry through constants: the network is globally tree-like.

## Sources

- François Bienvenu and Jean-Jil Duchamps, "A branching process with coalescence to model random phylogenetic networks", Electronic Journal of Probability 29 (2024), 1–48, <https://doi.org/10.1214/24-ejp1088>; numbering as in arXiv:2211.02407: Section 3 (Theorem 3.12 and Lemma 3.2) and Section 4 (Theorem 4.1, local weak limit).
