# Nucleotide-ratio threshold for compatible sequences of RNA secondary structures

**Setting.** A sequence is *compatible* with a secondary structure if every arc joins two nucleotides that can pair. Consider $r$-canonical secondary structures of length $n$ with minimum arc-length $\lambda$ ($1\le\lambda\le4$, $1\le r\le3$), counted by $s^{[r]}_\lambda(n)$, and let $\mu^{[r]}_\lambda,\sigma^{[r]}_\lambda$ be the mean and standard deviation per nucleotide of their number of arcs (which is asymptotically Gaussian). For a composition vector, let $s_{\cdot}(n)$ count the structures that admit at least one compatible sequence with that composition (counts $\lfloor p n\rfloor$, rounded consistently).

**Theorem.** In each case below, with the stated *effective pairing capacity* $q$,

$$\frac{\#\{\text{structures with a compatible sequence}\}}{s^{[r]}_\lambda(n)}=\Phi\!\Big(\frac{(q-\mu^{[r]}_\lambda)\sqrt n}{\sigma^{[r]}_\lambda}\Big)+O(n^{-1/2}),$$

where $\Phi$ is the standard normal distribution function:

1. *Purine–pyrimidine pairs* (alphabet $\{R,Y\}$, pairs $R$–$Y$), purine fraction $p\in(0,\tfrac12]$: $q=p$. Here a structure with $l$ arcs has a compatible sequence exactly when $l\le\min(\lfloor pn\rfloor,\lceil(1-p)n\rceil)$.
2. *Watson–Crick pairs* (A–U, C–G), composition $(p_1,p_2,p_3,p_4)$ for (A, U, C, G): $q=p_0=\min(p_1,p_2)+\min(p_3,p_4)$.
3. *Watson–Crick and wobble pairs* (A–U, C–G, G–U): $q=\bar p_0=\min\{\min(p_1,p_2)+p_4,\ \min(p_3,p_4)+p_2\}$.

Hence, if $q>\mu^{[r]}_\lambda$ then asymptotically almost every structure has a compatible sequence of that composition, and if $q<\mu^{[r]}_\lambda$ then asymptotically almost no structure does: the composition simplex splits into a convex region of "foldable" ratios and its complement.

## Expansion

A structure with $l$ arcs needs $l$ disjoint complementary pairs, so the compatibility question reduces to comparing $l$ with the largest number of pairs the composition can supply: $\min$ of the two partner counts for each pairing class, maximized over how wobble-capable nucleotides are allocated. Filtering the arc-count distribution by this cutoff and applying the arc-number central limit theorem gives the Gaussian cumulative form. For the realistic parameters $\lambda=4$, $r=3$ the threshold is $\mu^{[3]}_4=0.3113$; the average composition observed across RNA families, (0.208, 0.200, 0.271, 0.321) for (A, U, C, G), gives $p_0\approx0.47$, well inside the foldable region, so composition alone does not obstruct folding into typical structures.

## Depends on

- [Arc-number central limit theorem for canonical RNA secondary structures](arc-number-central-limit-theorem-for-canonical-secondary-structures.md)

## Sources

- C. L. Barrett, T. J. X. Li, C. M. Reidys, "RNA secondary structures having a compatible sequence of certain nucleotide ratios", arXiv:1603.03653 (2016), Section "Main results": Propositions 1, 2 and 3, Theorems 9, 10 and 11; Section "Discussion", <https://doi.org/10.48550/arXiv.1603.03653>.
