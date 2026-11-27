# Network separation and the complementary exposure pattern

**Setting.** As in [closest network proximity](closest-network-proximity-and-its-degree-matched-z-score.md), $G$ is a connected interactome with shortest-path distance $d$. For target sets $A, B \subseteq V$ of two drugs, write $\langle d_{AB}\rangle$ for the mean over all elements of $A \cup B$ (counted as in the closest measure) of the distance to the nearest element of the other set, and for a set $A$ with $|A| \ge 2$ write $\langle d_{AA}\rangle$ for the mean over $a \in A$ of $\min_{a' \in A \setminus\{a\}} d(a,a')$.

**Definition (separation).**

$$s_{AB} = \langle d_{AB}\rangle - \frac{\langle d_{AA}\rangle + \langle d_{BB}\rangle}{2}.$$

Negative $s_{AB}$ means the two target modules overlap or interleave; $s_{AB} \ge 0$ means they occupy topologically separate neighbourhoods.

**Definition (complementary exposure).** Given a disease module $C$, a drug pair $(A,B)$ shows the *complementary exposure* pattern when both drugs are proximal to the module, $Z_{CA} < 0$ and $Z_{CB} < 0$ (each significant), and their targets are separated, $s_{AB} \ge 0$. The working hypothesis of the source is that a drug combination is therapeutically effective only if it follows this pattern.

## Depends on

- [Closest network proximity and its degree-matched z-score](closest-network-proximity-and-its-degree-matched-z-score.md)

## Remarks

$\langle d_{AA}\rangle$ and $\langle d_{BB}\rangle$ measure how tightly each target set clusters; subtracting their mean from the between-set distance compares inter-module to intra-module spacing. If $A = B$ then $\langle d_{AB}\rangle = 0$ and $s_{AB} = -\langle d_{AA}\rangle \le 0$. The pattern was derived from approved hypertension and cancer combinations and used in the source to propose pairs such as sirolimus with dactinomycin.

## Sources

- Y. Zhou, Y. Hou, J. Shen, Y. Huang, W. Martin and F. Cheng, *Network-based drug repurposing for novel coronavirus 2019-nCoV/SARS-CoV-2*, Cell Discov. 6 (2020), 14. <https://doi.org/10.1038/s41421-020-0153-3> (PMCID: PMC7073332). Methods, "Network-based rational prediction of drug combinations", Eq. (3); Fig. 6a.
- J. Menche, A. Sharma, M. Kitsak, S. D. Ghiassian, M. Vidal, J. Loscalzo and A.-L. Barabási, *Uncovering disease-disease relationships through the incomplete interactome*, Science 347 (2015), 1257601. <https://doi.org/10.1126/science.1257601>
- F. Cheng, I. A. Kovács and A.-L. Barabási, *Network-based prediction of drug combinations*, Nat. Commun. 10 (2019), 1197. <https://doi.org/10.1038/s41467-019-09186-x>
