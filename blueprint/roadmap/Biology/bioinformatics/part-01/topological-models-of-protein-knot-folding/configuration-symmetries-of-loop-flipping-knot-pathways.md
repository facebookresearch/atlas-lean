# Configuration symmetries of loop-flipping knot pathways

**Setting.** A topological model of protein knot folding: an open chain forms a small red loop and a large green loop, each with some number of vertical twists; the blue terminus approaches so that the black arc passes in front of or behind the red arc; then the green loop flips over the red loop and the blue end while the blue end threads the red loop, in either order. The resulting projection (closed up by joining the termini) is a *configuration* written $XY(\varepsilon, a, b)$, where

- $X, Y \in \{L, R\}$ record whether the left or right side of the red loop ($X$) and of the green loop ($Y$) lies in front of the blue arc after threading;
- $\varepsilon \in \{+, -\}$ is the sign of the red-black crossing at the bottom ($+$ exactly when the black arc goes over the red arc), using the convention that a crossing is $+$ when its overcrossing has positive slope;
- $a, b \in \mathbb{Z}$ give the number and slope sign of the vertical twists in the red and green loops: $|a|$ twists whose crossings have slope sign $\operatorname{sign}(a)$, and similarly for $b$.

The census of the model takes $a, b \in \{0, \pm 1, \pm 2\}$, which gives $4 \cdot 2 \cdot 25 = 200$ configurations. Write $-K$ for the mirror image of a knot type $K$ and $-XY(\varepsilon, a, b)$ for the mirror image of a configuration.

**Lemma 1 (mirror images).** For all integers $a, b$,

$$RR(+, a, b) = -LL(-, -a, -b), \quad RR(-, a, b) = -LL(+, -a, -b),$$

$$RL(+, a, b) = -LR(-, -a, -b), \quad RL(-, a, b) = -LR(+, -a, -b).$$

**Theorem 1 (sixteen-fold equivalence).** Let $a, b$ be integers and $\varepsilon \in \{+, -\}$. If one of the configurations

$$RR(\varepsilon, a, b),\ RR(\varepsilon, b, a),\ RL(\varepsilon, a, b-1),\ LR(\varepsilon, b-1, a),\ RL(\varepsilon, b, a-1),\ LR(\varepsilon, a-1, b),\ LL(\varepsilon, a-1, b-1),\ LL(\varepsilon, b-1, a-1)$$

has knot type $K$, then all eight have knot type $K$, and the eight configurations

$$LL(-\varepsilon, -a, -b),\ LL(-\varepsilon, -b, -a),\ LR(-\varepsilon, -a, -b+1),\ RL(-\varepsilon, -b+1, -a),$$

$$LR(-\varepsilon, -b, -a+1),\ RL(-\varepsilon, -a+1, -b),\ RR(-\varepsilon, -b+1, -a+1),\ RR(-\varepsilon, -a+1, -b+1)$$

all have knot type $-K$. For an achiral knot $K$ all sixteen have type $K$.

## Expansion

Reflecting a projection in the plane of the paper interchanges over- and undercrossings. This swaps which side of each loop lies in front ($L \leftrightarrow R$) and negates the slope sign of every crossing, which gives Lemma 1. The second half of Theorem 1 is the first half composed with Lemma 1; the first half is proved in the SI Appendix of the source. A check against Table 1 of the source: $RR(+, 0, 0)$ is the right-handed trefoil $+3_1$, and Theorem 1 with $\varepsilon = +$, $a = b = 0$ predicts that $RL(+, 0, -1)$, $LR(+, -1, 0)$ and $LL(+, -1, -1)$ are also $+3_1$, which is what the table lists.

These relations reduce the knot typing of all $200$ configurations to a small number of computations; for example, the achiral figure-eight knot $4_1$ arises from exactly the $16$ configurations of a single family of Theorem 1, while $+5_2$ and $-5_2$ arise from $12$ each. Since several configurations give the same knot, the model predicts several distinct folding pathways for most knot types, consistent with protein families that share a knot but need not fold the same way.

## Sources

- E. Flapan, A. He, H. Wong, "Topological descriptions of protein folding", Proceedings of the National Academy of Sciences of the USA 116 (2019) 9360–9369, section 3 ("Our Proposed Theory of Knot Folding"), Lemma 1, Theorem 1 and Table 1, <https://doi.org/10.1073/pnas.1808312116>, PMCID PMC6510998.
