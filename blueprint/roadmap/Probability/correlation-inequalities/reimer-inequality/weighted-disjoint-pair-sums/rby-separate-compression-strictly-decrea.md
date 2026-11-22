# Down- and up-compressing two families can decrease disjoint pairs

There exist families $\mathcal{A}, \mathcal{B}$ of subsets of $\{0, 1\}$ and a coordinate $i \in \{0,1\}$ such that down-compressing $\mathcal{A}$ at $i$ and up-compressing $\mathcal{B}$ at $i$ strictly decreases the number of disjoint pairs:

$$\#\{(S, T) \in C_i^{\downarrow}(\mathcal{A}) \times C_i^{\uparrow}(\mathcal{B}) : S \cap T = \emptyset\} < \#\{(S, T) \in \mathcal{A} \times \mathcal{B} : S \cap T = \emptyset\}.$$

Here the down-compression $C_i^{\downarrow}$ replaces each $S \ni i$ by $S \setminus \{i\}$ when the latter is not already in the family, and the up-compression $C_i^{\uparrow}$ replaces each $T \not\ni i$ by $T \cup \{i\}$ when the latter is not already in the family.
