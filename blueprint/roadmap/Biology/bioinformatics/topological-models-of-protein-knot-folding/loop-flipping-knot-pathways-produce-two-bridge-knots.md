# Loop-flipping knot pathways produce two-bridge knots

**Setting.** The loop-flipping model of protein knot folding, whose final projections are the configurations $XY(\varepsilon, a, b)$ with $X, Y \in \{L, R\}$ (front side of the red and green loops), $\varepsilon \in \{+, -\}$ (sign of the red-black crossing) and twist parameters $a$ (red loop) and $b$ (green loop). A configuration is *consistent with a twisted hairpin pathway* if, fixing the blue end and pulling down on the red end, the red loop and all red twisting disappear and leave a single red-black crossing; then the knotting is due entirely to threading the green loop, as in Taylor's twisted hairpin theory.

**Theorem 2 (bridge number).** For all integers $a, b$, every knot obtained by the steps of the model can be deformed to a conformation whose projection has only two local maxima. Equivalently, every such knot is a two-bridge knot.

**Knot census.** With $a, b \in \{0, \pm 1, \pm 2\}$, the $200$ configurations produce the unknot and exactly $14$ nontrivial knot types up to mirror image:

$$3_1,\ 4_1,\ 5_1,\ 5_2,\ 6_1,\ 6_2,\ 6_3,\ 7_2,\ 7_5,\ 7_6,\ 7_7,\ 8_8,\ 8_{14},\ 9_{23}.$$

These include all knot types found so far in proteins ($\pm 3_1$, $4_1$, $-5_2$, $+6_1$); of the $84$ prime knots with at most nine crossings, $50$ are two-bridge and these $14$ are the ones reached. Every type except $9_{23}$ arises from more than one configuration.

**Theorem 3 (twisted hairpin configurations).** For any value of the green twist parameter $b$, the configurations consistent with a twisted hairpin pathway are exactly

$$RR(+, 0, b),\ RR(-, 1, b),\ RL(+, 0, b),\ RL(-, 1, b),\ LR(-, 0, b),\ LR(+, -1, b),\ LL(-, 0, b),\ LL(+, -1, b).$$

## Depends on

- [Configuration symmetries of loop-flipping knot pathways](configuration-symmetries-of-loop-flipping-knot-pathways.md)

## Expansion

Theorem 2 is a statement about knot type, not about the native fold: a knotted protein's actual conformation has many crossings and maxima, but its closed-up knot type admits a two-maximum projection, which places it in the two-bridge (rational) family. Twist knots, the only family allowed by Taylor's twisted hairpin theory, are two-bridge, so the model strictly enlarges that family; $5_1$, $6_2$ and $6_3$ are two-bridge but not twist knots, so the model, unlike the twisted hairpin theory, does not rule them out.

The first four configurations of Theorem 3 are those of Fig. 7 of the source, for which pulling the red end slides the red arc along the blue and black arcs until the red loop vanishes; the last four are their mirror images under the reflection rule $RR(+, a, b) = -LL(-, -a, -b)$ and its companions. Combined with knot fingerprints (the knot types of all subchains obtained by clipping residues from the termini), Theorem 3 decides which pathways are compatible with crystal structures: the data support twisted hairpin folding for the $3_1$-knotted proteins and the $4_1$-knotted ketol-acid reductoisomerases, while no configuration for $+6_1$ is consistent with a twisted hairpin pathway, and the fingerprint of the $+6_1$-knotted dehalogenase instead agrees with the loop-flipping configuration $RR(-, 2, -1)$ found in simulation.

## Sources

- E. Flapan, A. He, H. Wong, "Topological descriptions of protein folding", Proceedings of the National Academy of Sciences of the USA 116 (2019) 9360–9369, Theorems 2–3, Table 1 and sections 4–6, <https://doi.org/10.1073/pnas.1808312116>, PMCID PMC6510998.
