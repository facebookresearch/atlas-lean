# Expected common branch length of two random tip samples

Let $T$ be a phylogenetic tree with tip set $S$, $|S| = s$, and edge weights $w_e$. For a tip sample $R$ let $T(R)$ be the minimum subtree spanning $R$. For samples $A, B$ the **common branch length** is

$$\mathrm{CBL}(T,A,B) = \sum_{e \in T(A)\cap T(B)} w_e,$$

a similarity measure underlying PhyloSor and UniFrac. For an edge $e$ let $s(e)$ be the number of tips on one side of $e$.

**Theorem.** If $A$ and $B$ are drawn independently and uniformly among tip subsets of sizes $a$ and $b$, then

$$\mathbb{E}\,\mathrm{CBL}(T,a,b) = \sum_{e} w_e\left(1 - \frac{\binom{s(e)}{a} + \binom{s - s(e)}{a}}{\binom{s}{a}}\right)\left(1 - \frac{\binom{s(e)}{b} + \binom{s - s(e)}{b}}{\binom{s}{b}}\right)$$

(Tsirogiannis and Sandel 2016, Theorem 3). A closed form for the standard deviation in terms of pairs of edges also exists (Theorem 4), giving the standardized common length index $\mathrm{CLI} = (\mathrm{CBL} - \mathbb{E}\,\mathrm{CBL})/\mathrm{sd}\,\mathrm{CBL}$ (Eq. 8).

## Expansion

By linearity, $\mathbb{E}\,\mathrm{CBL} = \sum_e w_e \Pr[e \in T(A)]\Pr[e\in T(B)]$ using independence of $A$ and $B$. An edge lies outside the spanning subtree of $A$ exactly when all of $A$ falls on one side of it, which happens for $\binom{s(e)}{a} + \binom{s-s(e)}{a}$ of the $\binom{s}{a}$ equally likely samples.

## Sources

- C. Tsirogiannis and B. Sandel, *Fast computations for measures of phylogenetic beta diversity*, PLoS ONE 11(4) (2016), e0151167, Eq. (8) and Theorems 3–4. <https://doi.org/10.1371/journal.pone.0151167> (PMCID: PMC4824508)
