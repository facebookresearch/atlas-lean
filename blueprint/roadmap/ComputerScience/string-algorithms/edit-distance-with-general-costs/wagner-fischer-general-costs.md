# The Wagner-Fischer recurrence for general costs

For every cost function, $d(\varepsilon, \varepsilon) = 0$, $d(ax, \varepsilon) = \mathrm{del}(a) + d(x, \varepsilon)$, $d(\varepsilon, by) = \mathrm{ins}(b) + d(\varepsilon, y)$, and

$$
d(ax, by) = \min\big(\mathrm{sub}(a,b) + d(x, y),\; \mathrm{del}(a) + d(x, by),\; \mathrm{ins}(b) + d(ax, y)\big).
$$

The dynamic program over pairs of suffixes therefore computes $d(x, y)$ and an optimal script with $O((|x| + 1)(|y| + 1))$ table entries, and the result is the least cost of any script; on the word RAM it runs in $O((|x|+1)(|y|+1))$ instructions.

## Depends on

- [Edit distance under general letter costs](general-cost-edit-distance.md)
- [The word-RAM model](../../../TheoryOfComputation/fine-grained-complexity/fine-grained-hypotheses/the-word-ram-model.md)

## Proof depends on

- [Edit distance algorithm](../edit-distance/edit-distance.md)

## Sources

- R. A. Wagner and M. J. Fischer, "The String-to-String Correction Problem", Journal of the ACM 21(1), 1974.
- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd ed., MIT Press, 2009.
