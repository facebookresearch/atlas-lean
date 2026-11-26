# Distinct-position 3SUM as finitely many three-set problems

Call $(P, Q, R)$ a **three-set instance** if $P, Q, R$ are finite sets of integers, with solution any $(p, q, r) \in P \times Q \times R$ with $p + q + r = 0$. A distinct-position 3SUM input $x$ has a solution if and only if one of the following holds: (i) some value $v$ occurs at least three times with $3v = 0$; (ii) some value $v$ occurs at least twice and $-2v$ occurs at a third position; (iii) one of a constant number of explicit three-set instances, built from the set of values of $x$, its doubled set and its zero set, has a solution with three distinct values. All sets involved have size at most $n$ and entries bounded by $2\max_i |x_i|$.

## Proof sketch

Classify a solution by how many of its three values coincide. Distinct values give a three-set solution on the value set; two equal values need multiplicity two; three equal values force $v = 0$.

## Depends on

- [Distinct-position 3SUM](distinct-position-three-sum.md)

## Sources

- T. M. Chan and Q. He, "Reducing 3SUM to Convolution-3SUM", Symposium on Simplicity in Algorithms (SOSA), 2020.
