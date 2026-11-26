# Covariance-matched joint tables on a fingerprint tree network

Let $X_1, \dots, X_n \in \{0,1\}$ indicate molecular properties of an unknown compound, with predicted marginals $p_i = P(X_i = 1) \in [0,1]$. Let $T = (V, E)$ be a tree on $V = \{1,\dots,n\}$ oriented away from a root $r$ (an arborescence). The **tree Bayesian network** joint law is

$$P(X_1, \dots, X_n) = P(X_r)\prod_{(i,j)\in E} P(X_j \mid X_i) = P(X_r)\prod_{(i,j)\in E}\frac{P(X_i, X_j)}{P(X_i)} .$$

For an edge $(i,j)$ the pair table $q_{ab} = P(X_i = a, X_j = b)$ must satisfy $q_{11} + q_{10} = p_i$, $q_{11} + q_{01} = p_j$, $\sum q_{ab} = 1$, leaving one degree of freedom, which is used to match a target covariance $c_{ij} \in \mathbb{R}$ through $q_{11} = c_{ij} + p_i p_j$ when possible. Define the clamped choice

$$q_{11} = \max\big\{0,\ p_i + p_j - 1,\ \min\{p_i,\ p_j,\ c_{ij} + p_i p_j\}\big\},$$

with $q_{10} = p_i - q_{11}$, $q_{01} = p_j - q_{11}$, $q_{00} = 1 - q_{11} - q_{10} - q_{01}$.

**Lemma 1 (validity).** For all $p_i, p_j \in [0,1]$ and $c_{ij} \in \mathbb{R}$, the four numbers $q_{11}, q_{10}, q_{01}, q_{00}$ lie in $[0,1]$, so they form a joint distribution with the prescribed marginals.

**Lemma 2–3 (optimality of the clamp).** If $q_{11} < c_{ij} + p_ip_j$, no larger value of $q_{11}$ yields a valid table with these marginals; if $q_{11} > c_{ij} + p_ip_j$, no smaller value does. Hence the clamped table has covariance $q_{11} - p_ip_j$ as close to $c_{ij}$ as the marginals allow.

## Expansion

Valid tables with the given marginals are exactly those with $q_{11}$ in the Fréchet interval $[\max(0, p_i + p_j - 1),\ \min(p_i, p_j)]$: $q_{10}, q_{01} \ge 0$ force $q_{11} \le \min(p_i,p_j)$ and $q_{00} = 1 - p_i - p_j + q_{11} \ge 0$ forces $q_{11} \ge p_i + p_j - 1$. The clamp projects the target $c_{ij} + p_ip_j$ onto this interval (the lower bound is never above the upper bound when $p_i, p_j \in [0,1]$), which gives all three lemmas. In the application the tree is a maximum-mutual-information spanning tree estimated from fingerprints of database structures, target covariances come from prediction errors on training compounds, and the resulting joint law replaces the independence assumption when scoring how well each candidate's fingerprint explains the predicted one.

## Sources

- M. Ludwig, K. Dührkop, S. Böcker, "Bayesian networks for mass spectrometric metabolite identification via molecular fingerprints", Bioinformatics 34(13) (2018) i333–i340, Eqs. (3)–(6), Lemmas 1–3 and Section 4.1, <https://doi.org/10.1093/bioinformatics/bty245>, PMCID PMC6022630.
