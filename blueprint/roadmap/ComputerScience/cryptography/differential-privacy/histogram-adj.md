# Neighbouring histograms

A database over a finite universe $U$ of record types is a histogram $x : U \to \mathbb{N}$, where
$x(u)$ counts the records of type $u$. Two histograms are neighbours when
$\|x - y\|_1 = \sum_{u} |x(u) - y(u)| \le 1$: they differ by adding or removing at most one record.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 2.3 and Definition 2.4.
