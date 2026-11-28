# Three-way Sørensen and Czekanowski indices and the three-quarters bound

A 3-way network is a hypergraph $G = (V, E)$ whose edges are 3-element subsets $\{v_x, v_y, v_z\}$ of the node set. To weight an edge, represent each object (for instance a genome) by a vector of nonnegative feature counts (gene-family copy numbers). For objects $A, B, C$ viewed as feature sets, with $a, b, c$ their numbers of features, $ab, ac, bc$ the numbers shared by each pair and $abc$ the number shared by all three, the three-way Sørensen index is

$$S_3(ABC) = \frac{3}{2}\cdot\frac{ab + ac + bc - abc}{a + b + c},$$

equivalently, for binarized vectors $X_B, Y_B, Z_B$,

$$S_3(X,Y,Z) = \frac{\tfrac32\sum_i\left(\min(X_{B,i}, Y_{B,i}) + \min(X_{B,i}, Z_{B,i}) + \min(Y_{B,i}, Z_{B,i}) - \min(X_{B,i}, Y_{B,i}, Z_{B,i})\right)}{\sum_i (X_{B,i} + Y_{B,i} + Z_{B,i})}.$$

The three-way Czekanowski index $C_3(X,Y,Z)$ is the same expression applied to the raw count vectors $X, Y, Z$. Both extend the pairwise indices $S_2 = 2\,ab/(a+b)$ and $C_2(X,Y) = 2\sum_i \min(X_i, Y_i)/\sum_i (X_i + Y_i)$.

1. For integers $a, b, c$: $\min(a,b) + \min(a,c) - \min(a,b,c) \le a$.
2. If no feature is present in all three objects ($abc = 0$), then $S_3(ABC) \le \tfrac34$, with equality when every feature lies in exactly two of the objects.
3. If no gene family is present in all three species, i.e. $\sum_i \min(X_i, Y_i, Z_i) = 0$, then $C_3(X,Y,Z) \le \tfrac34$.

Consequently, thresholding a 3-way Sørensen or Czekanowski network above $0.75$ keeps only triplets with a genuine three-way intersection.

## Expansion

With $abc = 0$, each feature of $A \cup B \cup C$ lies in one or two of the sets, so $a + b + c = 2(ab + ac + bc) + \bar a + \bar b + \bar c$, where $\bar a, \bar b, \bar c$ count features unique to one object; hence $S_3 = \tfrac32 (ab+ac+bc)/(2(ab+ac+bc) + \bar a + \bar b + \bar c) \le \tfrac34$. For the counts, part 1 applied coordinatewise with each vector in the role of $a$, summed and added, shows that twice the sum of pairwise minima is at most $\sum_i (X_i + Y_i + Z_i)$ when the triple minima vanish, which gives the same bound.

## Sources

- D. A. Weighill and D. A. Jacobson, "3-way networks: application of hypergraphs for modelling increased complexity in comparative genomics", *PLOS Computational Biology* 11 (2015), e1004079, Definition 1, Eqs. (2)–(9), Theorem 1, Lemma 1 and Theorem 2. <https://doi.org/10.1371/journal.pcbi.1004079> (PMC4376783)
