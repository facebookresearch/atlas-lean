# Saturation function for continuous patterns

For a real number $n$ and a set
$P \subseteq \mathbb{R}^2$, call an open set $S \subseteq [0, n]^2$ saturating for $P$ if $S$
does not contain $P$ but every open set $S' \subseteq [0, n]^2$ properly containing $S$ contains
$P$ (containment in the sense of point-set pattern containment). The saturation function
$\operatorname{osat}(n, P)$ is the infimum of the Lebesgue measures $\mu_2(S)$ over all sets $S$
saturating for $P$, and is $0$ when no saturating set exists.

The paper leaves $\operatorname{osat}(n, P)$ undefined when no saturating set exists.

## Sources

- Jesse Geneson, *Continuous Turán Numbers*, INTEGERS 24 (2024), Article A1, Section 6 (definition of `osat(n, P)`).
