# Score of an induced pairwise alignment

Let $\sigma$ assign an integer score to each
pair of letters and let $g$ be an integer gap score. For a multiple alignment $A$ of $k$
sequences and rows $i, j < k$, the score (with respect to $\sigma$ and $g$) of the pairwise
alignment induced by $A$ on rows $i$ and $j$ equals the sum, over all columns $c$ of $A$, of the
column score of the pair $(c_i, c_j)$.
