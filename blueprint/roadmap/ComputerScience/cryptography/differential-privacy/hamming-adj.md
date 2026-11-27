# Neighbouring row databases

A database of $n$ rows from a set $U$ is a list $S : \{0, \dots, n - 1\} \to U$. Two such
databases are neighbours when they differ in at most one row, i.e. their Hamming distance is at most
$1$. This is the relation used for data sets of i.i.d. samples, for instance in adaptive data
analysis.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Section 2.3 (databases as ordered lists of rows, compared by Hamming distance).
