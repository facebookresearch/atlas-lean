# Folding recurrence for mean isotope peak masses

For a molecule made of $l$ atoms, let $X_i$ be the (random) exact mass and $Y_i \in \mathbb{N}$ the mass number of atom $i$, drawn independently from the natural isotope distribution of its element. The molecule's mass is $X = \sum_i X_i$ and its nominal mass is $Y = \sum_i Y_i$. If $N$ is the monoisotopic nominal mass, the **isotopic distribution** is $p_k := \mathbb{P}(Y = N + k)$, $k \ge 0$, and the **mean peak mass** of the $+k$ peak is

$$m_k := \mathbb{E}(X \mid Y = N + k).$$

The pair $(p_k, m_k)_{k \ge 0}$ is the molecule's isotope pattern.

**Theorem (folding of distributions and mean masses).** Let two independent molecules have isotope patterns $(p_k, m_k)$ and $(q_k, m_k')$ with monoisotopic nominal masses $N$ and $N'$. Their union $Z = Y + Y'$ has monoisotopic nominal mass $N + N'$, isotopic distribution

$$r_k = \sum_{i=0}^{k} p_i\, q_{k-i},$$

and, whenever $r_k > 0$, mean peak masses

$$\tilde m_k = \frac{1}{r_k} \sum_{i=0}^{k} p_i\, q_{k-i}\, \bigl(m_i + m'_{k-i}\bigr).$$

Consequences:

- for an element with two isotopes (H, C, N) and monoisotope probability $p$, $E_l$ has the binomial pattern $p_k = \binom{l}{k} p^{l-k} (1-p)^k$, computable for $k < K$ by the ratio recurrence $p_{k+1} = p_k \cdot \frac{l-k}{k+1} \cdot \frac{1-p}{p}$ in $O(K)$;
- for elements with more isotopes (O, S), $E_l$ is obtained by repeated folding with a square-and-multiply scheme, in $O(K^2 \log l)$ time when each distribution is truncated to its first $K$ peaks;
- a molecule over $n$ elements is the fold of its per-element patterns, in $O(n K^2)$ time, and the mean masses come at the same cost as the distribution itself.

## Expansion

The event $\{Z = N + N' + k\}$ is the disjoint union over $i$ of $\{Y = N + i,\ Y' = N' + k - i\}$, which gives $r_k$ by independence. On each piece, $\mathbb{E}(X + X' \mid Y = N+i, Y' = N'+k-i) = m_i + m'_{k-i}$, again by independence, and averaging over the pieces with weights $p_i q_{k-i} / r_k$ gives $\tilde m_k$. Folding mean masses this way replaces a linear dependence on the number of atoms (summing over isotope species) by a logarithmic one. The simulated pattern $(r_k, \tilde m_k)$ is then compared with the measured peaks: mass deviations, taken relative to the monoisotopic peak to cancel calibration shift, are scored by a two-sided normal tail $\mathrm{erfc}$, and log intensity ratios $\log(f_j / r_j)$ are scored the same way.

## Sources

- S. Böcker, M. C. Letzel, Zs. Lipták, A. Pervukhin, "SIRIUS: decomposing isotope patterns for metabolite identification", Bioinformatics 25 (2009) 218–224, Section 2 (isotope patterns), Section 3.3 (simulating isotope patterns, Theorem 1) and Section 3.4 (scoring), <https://doi.org/10.1093/bioinformatics/btn603> (PMC2639009).
