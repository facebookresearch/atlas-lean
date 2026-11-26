# Validity of Monte Carlo permutation p-values

Let a finite group $G$ (with its discrete σ-algebra) act measurably on a measurable space $\Omega$, let $\mu$ be a probability measure on $\Omega$ invariant under the action, $T : \Omega \to \mathbb{R}$ measurable and $B \in \mathbb{N}$. Let $g_1, \dots, g_B$ be drawn independently and uniformly from $G$, independently of the data $\omega \sim \mu$. Then the [Monte Carlo permutation p-value](monte-carlo-permutation-pvalue.md)

$$\frac{1 + \#\{b : T(g_b \cdot \omega) \ge T(\omega)\}}{B + 1}$$

is a valid p-value under the joint law $\mu \otimes \mathrm{Unif}(G)^{\otimes B}$.

## Sources

- B. Phipson and G. K. Smyth, *Permutation p-values should never be zero*, Stat. Appl. Genet. Mol. Biol. 9 (2010), Article 39.
- J. Hemerik and J. Goeman, *Exact testing with random permutations*, TEST 27 (2018), 811–825.
