# Nesting of dyadic intervals

For levels $j \le k$ and every $x \in \mathbb{R}$,

$$\lfloor 2^j x \rfloor = \big\lfloor \lfloor 2^k x \rfloor / 2^{k-j} \big\rfloor,$$

with integer division rounding down. Hence two points in the same level-$k$ [dyadic interval](dyadic-interval.md) lie in the same level-$j$ interval: a finer dyadic interval is contained in exactly one interval of each coarser level. This is the nesting property of dyadic cubes (any two are nested or disjoint) used throughout T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014, §1.A and Lemma 1.3, in dimension one. The proof is the identity $\lfloor a / n \rfloor = \lfloor \lfloor a \rfloor / n \rfloor$ for a positive integer $n$.

## Background

- [Dyadic index](dyadic-index.md): the index $\lfloor 2^k x \rfloor$ of the statement.

## Sources

- T. Hytönen, *Dyadic analysis and weights*, lecture notes, University of Helsinki, version of 2 May 2014 (a secondary source: lecture notes presenting the dyadic theory of C. Fefferman and E. M. Stein, *Some maximal inequalities*, Amer. J. Math. 93 (1971), 107–115, and of E. M. Stein, *Harmonic Analysis*, Princeton University Press, 1993).
