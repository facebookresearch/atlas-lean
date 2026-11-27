# Insertion-deletion distance and longest common subsequences

Under the costs $\mathrm{del} = \mathrm{ins} = 1$ and $\mathrm{sub}(a, b) = 0$ if $a = b$ and $\ge 2$ otherwise, the edit distance satisfies

$$
d(x, y) + 2\,\mathrm{lcs}(x, y) = |x| + |y|,
$$

where $\mathrm{lcs}(x, y)$ is the length of a longest common subsequence.

## Proof sketch

A script without substitutions of distinct letters keeps a common subsequence and deletes and inserts the rest; a substitution of distinct letters can be replaced by a deletion and an insertion at no greater cost.

## Depends on

- [Edit distance under general letter costs](general-cost-edit-distance.md)
- [Longest common subsequence by dynamic programming](../../dynamic-programming/longest-common-subsequence/longest-common-subsequence.md)

## Proof depends on

- [The Wagner-Fischer recurrence for general costs](wagner-fischer-general-costs.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
- R. A. Wagner and M. J. Fischer, "The String-to-String Correction Problem", Journal of the ACM 21(1), 1974.
