# The dissimilarity index is a total-variation distance

For two groups with counts $a_1, \dots, a_m \ge 0$ and $b_1, \dots, b_m \ge 0$ across $m$ areas and positive totals $A = \sum_k a_k$, $B = \sum_k b_k$, the dissimilarity index $D = \tfrac12\sum_k |a_k/A - b_k/B|$ is the total-variation distance $\max_{E \subseteq \{1, \dots, m\}} |\sum_{k \in E} a_k/A - \sum_{k \in E} b_k/B|$ between the two distributions over areas, attained at $E = \{k : a_k/A > b_k/B\}$. Hence $0 \le D \le 1$, $D = 0$ exactly when the two distributions coincide, and $D = 1$ exactly when no area has members of both groups. Reading $D$ as the fraction of one group that would have to move is a further interpretation with its own conventions.

## Background

- [Total variation and Pinsker's inequality](../../InformationTheory/information-inequalities/total-variation-and-pinsker-s-inequality/README.md): total variation for general measures.

## Sources

- The statement is derived on this page from its definitions and the linked results; no external source is followed.
