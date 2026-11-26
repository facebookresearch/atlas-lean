# Labeled tableaux of a given shape

For a finite list $\alpha = (\alpha_1, \dots, \alpha_\ell)$ of natural numbers and a natural number $r$, the set $\Lambda(\alpha, r)$ of labeled tableaux of shape $\alpha$ consists of the tuples $(S_1, \dots, S_\ell)$ of subsets of $\{0, 1, \dots, r-1\}$ with $|S_j| = \alpha_j - 1$ for each $j$, the subtraction truncated, so $|S_j| = 0$ when $\alpha_j = 0$. The set $S_j$ records row $j$ of the tableau: an empty first box followed by $\alpha_j - 1$ strictly increasing labels. For the empty shape, $\Lambda(\emptyset, r)$ has the single empty tuple.

## Sources

- Molly Lynch and Michael Weselcouch, *A Generalized Hockey Stick Theorem*, J. Integer Seq. 28 (2025), Article 25.7.7, Section 2.3 (labeled tableaux), <https://cs.uwaterloo.ca/journals/JIS/VOL28/Weselcouch/wesel8.html>.
