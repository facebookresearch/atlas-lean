# Subset-sum query

For a database $d \in \{0,1\}^n$ of one bit per row and a set of rows $q \subseteq \{0, \dots, n - 1\}$, the subset-sum query has the exact answer $a_q(d) = \sum_{i \in q} d_i$, the number of rows in $q$ whose bit is $1$.

## Sources

- I. Dinur and K. Nissim, "Revealing information while preserving privacy", *Proceedings of the 22nd ACM PODS*, 2003, pp. 202–210, Definition 1
- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf>, Section 8.1 (the query given by the characteristic vector $S$ of $q$, with answer $\sum_i d_i S_i$)
