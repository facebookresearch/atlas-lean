# Interaction distance: normalized interaction information for genetic interactions

**Setting.** Let $X, Y$ be finite random variables encoding genotypes at two markers and $Z$ a finite (binned) phenotype. Write $H$ for Shannon entropy and $I$ for mutual information.

**Interaction information.** With the sign convention that synergy is positive,

$$II(X; Y; Z) = I(X; Y \mid Z) - I(X; Y),$$

the change in shared information between the markers when the phenotype is conditioned on. $II > 0$ indicates synergy: the pair carries more information about $Z$ jointly than singly. $II < 0$ indicates redundancy. The measure is symmetric in all three variables but unnormalized, so when a marker has low entropy (small minor allele frequency) even a deterministic interaction has $II$ close to $0$.

**Information distance.** Normalize mutual information by the larger entropy,

$$D(X, Y) = 1 - \frac{I(X; Y)}{\max\{H(X), H(Y)\}} \in [0, 1],$$

which is a metric and vanishes iff each variable is a function of the other. The conditional distance $D(X, Y \mid Z)$ is defined with every quantity conditioned on $Z$. $D$ decreases as dependence grows.

**Interaction distance.**

$$ID(X, Y; Z) = D(X, Y) - D(X, Y \mid Z).$$

It is symmetric in the markers $X, Y$ but not in the phenotype $Z$, and positive values again mean synergy.

**Theorem (properties of ID).** For finite random variables $X, Y, Z$:

1. $-1 \le ID(X, Y; Z) \le 1$.
2. $ID = 1$ iff $X$ and $Y$ are independent ($D(X, Y) = 1$) and conditionally functionally equivalent given $Z$ ($D(X, Y \mid Z) = 0$). For example, $X, Y$ are independent and $Z = X \oplus Y$, so that each of $X, Y$ is determined by the other together with $Z$.
3. $ID \to -1$ iff $D(X, Y) \to 0$ and $D(X, Y \mid Z) \to 1$: the markers are functionally related to each other but conditionally independent given $Z$, as when $Z$ determines both.

For $X, Y$ independent uniform bits and $Z = X \oplus Y$, both $II$ and $ID$ equal $1$. If the marginals of $X, Y$ are skewed so that their entropies drop, $II$ falls while $ID$ stays at $1$. That is why the normalized measure keeps power for rare variants.

**Permutation nulls.** For a marker pair the significance of $ID$ is assessed by permutation. Permuting both markers tests "no marginal effects and no interaction". Permuting only the marker without a marginal effect tests "no interaction, one main effect". Permuting each marker within the strata of the phenotype leaves $H(Z \mid X)$ and $H(Z \mid Y)$ unchanged, so its null is "no interaction" whatever the marginal effects.

## Depends on

- [Mutual information of a finite joint law](../../../../../../InformationTheory/entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)
- [Conditional mutual information of a finite joint law](../../../../../../InformationTheory/entropy-and-mutual-information/conditional-mutual-information/finite-conditional-mutual-information.md)

## Expansion

Property 1 holds because $ID$ is a difference of two quantities in $[0, 1]$. For property 2, $ID = 1$ forces $D(X, Y) = 1$, i.e. $I(X; Y) = 0$, and $D(X, Y \mid Z) = 0$, i.e. $I(X; Y \mid Z) = \max\{H(X \mid Z), H(Y \mid Z)\}$, so given $Z$ each marker determines the other. Independence of $X$ and $Y$ is compatible with this, as the XOR example shows. Property 3 is the mirror case. Normalizing by the larger entropy, rather than the smaller, ensures that zero distance means a two-way functional relation, not just that the lower-entropy variable is determined. On yeast and mouse crosses with near-50% allele frequencies, $II$ and $ID$ behave alike. On simulated human interaction models with heterogeneous minor allele frequencies, $ID$ separates true interactions from noise better.

## Sources

- T. M. Ignac, A. Skupin, N. A. Sakhanenko, D. J. Galas, "Discovering pair-wise genetic interactions: an information theory-based approach", PLoS ONE 9 (2014) e92310, Equations (1)–(4), Methods sections "Different normalizations", "Properties of the interaction distance" (Theorems 1 and 2) and "Permutation tests" (Tests I–III), <https://doi.org/10.1371/journal.pone.0092310> (PMC3966778).
