# At most two modal tables in a fixed-score class

**Setting.** Consider $3\times 3$ prediction–observation tables with rows $q_+, q_-, q_0$ (predicted up, down, unregulated), columns $n_+, n_-, n_0$ (observed up, down, unchanged), fixed margins, and probability under the [generalized hypergeometric null](quaternary-score-and-its-hypergeometric-null.md)

$$P(T) \propto \frac{1}{\prod_{a,b} n_{ab}!}.$$

Let $S(T) = n_{++} + n_{--} - n_{+-} - n_{-+}$ be the correctness score, and let $\mathcal{M}[S, n_{++}, n_{--}]$ be the set of tables with given score $S$ and given cells $n_{++}$, $n_{--}$. Within this class the move

$$\sigma_1:\ (n_{-+},\,n_{+-},\,n_{+0},\,n_{-0},\,n_{0+},\,n_{0-}) \mapsto (n_{-+}-1,\,n_{+-}+1,\,n_{+0}-1,\,n_{-0}+1,\,n_{0+}+1,\,n_{0-}-1),$$

which preserves all margins, $S$, $n_{++}$ and $n_{--}$, and its inverse connect all tables, so the class is a one-parameter family indexed by $n_{-+}$.

**Theorem.** In every class $\mathcal{M}[S, n_{++}, n_{--}]$ there are at most two tables of maximal probability, and if there are two they are adjacent (differ by one application of $\sigma_1$). Along the family the probability is unimodal.

## Expansion

Fixing $S$, $n_{++}$ and $n_{--}$ fixes $n_{+-} + n_{-+}$; with the margins this leaves one free cell, say $n_{-+}$, and every other cell is an affine function of it. The ratio of probabilities of neighbouring tables is a ratio of products of linear functions of $n_{-+}$,

$$\frac{P(n_{-+}+1)}{P(n_{-+})} = \frac{n_{+-}\,n_{-0}\,n_{0+}}{(n_{-+}+1)(n_{+0}+1)(n_{0-}+1)},$$

which is nonincreasing in $n_{-+}$ because each numerator factor decreases and each denominator factor increases along the family. Hence the probability rises, possibly stays level for one step when the ratio equals $1$, and then falls. This structure lets an algorithm locate the mode of each class by a few moves and add only the tables of non-negligible probability around it, approximating tail probabilities of the score far faster than the $O(n^4)$ full enumeration.

## Depends on

- [Quaternary score and its generalized hypergeometric null](quaternary-score-and-its-hypergeometric-null.md)

## Sources

- Fakhry CT, Choudhary P, Gutteridge A, Sidders B, Chen P, Ziemek D, Zarringhalam K, "Interpreting transcriptional changes using causal graphs: new methods and their practical utility on public networks", BMC Bioinformatics (2016), Methods, "Model", Definitions 1–2, Theorem 1 and Eqs. (9)–(10), <https://doi.org/10.1186/s12859-016-1181-8>, PMCID PMC4995651.
