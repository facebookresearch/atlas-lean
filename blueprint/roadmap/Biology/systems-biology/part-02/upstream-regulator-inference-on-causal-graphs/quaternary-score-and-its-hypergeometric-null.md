# Quaternary score and its generalized hypergeometric null

**Table.** Fix a candidate regulator $X$ with putative positive direction. Each of $N$ genes receives a prediction in $\{+,-,r,0\}$ (predicted up, predicted down, regulated by an unsigned edge, not regulated) and an observation in $\{+,-,0\}$ (up, down, unchanged). Let $n_{ab}$ count genes with prediction $a$ and observation $b$, with row margins $q_+, q_-, q_r, q_0$ and column margins $n_+, n_-, n_0$; the margins are fixed by the network and the expression data.

**Null distribution.** Under random assignment of the observed labels given the margins,

$$P(T) = \frac{\binom{q_+}{n_{++},\,n_{+-},\,n_{+0}}\binom{q_-}{n_{-+},\,n_{--},\,n_{-0}}\binom{q_r}{n_{r+},\,n_{r-},\,n_{r0}}\binom{q_0}{n_{0+},\,n_{0-},\,n_{00}}}{\binom{N}{n_+,\,n_-,\,n_0}},$$

a product of multinomial coefficients over the multinomial count of all labelings. The significance of an observed score $S_0$ is $\sum_{T:\,S(T) \ge S_0}P(T)$.

**Scores.**

- Enrichment score (unsigned edges only): $ES(T) = n_{r+} + n_{r-}$. By Vandermonde's identity

$$P(ES = S_0) = \frac{\binom{q_r}{S_0}\binom{q_0}{n_+ + n_- - S_0}}{\binom{N}{n_+ + n_-}},$$

the hypergeometric law of Fisher's exact test.
- Correctness (ternary) score (signed edges only, $q_r = 0$): $CS(T) = n_{++} + n_{--} - (n_{+-} + n_{-+})$.
- Quaternary score (mixed networks): $QS(T) = n_{++} + n_{--} + n_{r+} + n_{r-} - (n_{+-} + n_{-+})$.

The quaternary score reduces to the enrichment score when no edge is signed and to the correctness score when every edge is signed. The tables have $1$, $4$ and $6$ degrees of freedom for the three scores, so brute-force enumeration of the score distribution costs $O(n)$, $O(n^4)$ and $O(n^6)$.

## Expansion

With all margins fixed, a table is determined by how the $n_+$ up-, $n_-$ down- and $n_0$ unchanged labels are distributed among the four prediction groups; the numerator counts the labelings producing a given table. For the enrichment score only the split of the $n_+ + n_-$ changed genes between the unsigned group and the unpredicted group matters, and summing the full table probability over the remaining free cells collapses it to a single hypergeometric term. Adding a constant combination of the free cells to a score shifts but does not reshape its distribution, which is why the quaternary score can count unsigned evidence without changing the inference machinery.

## Sources

- Fakhry CT, Choudhary P, Gutteridge A, Sidders B, Chen P, Ziemek D, Zarringhalam K, "Interpreting transcriptional changes using causal graphs: new methods and their practical utility on public networks", BMC Bioinformatics (2016), Methods, "Approach", Eqs. (1)–(6) and Table 1, <https://doi.org/10.1186/s12859-016-1181-8>, PMCID PMC4995651.
