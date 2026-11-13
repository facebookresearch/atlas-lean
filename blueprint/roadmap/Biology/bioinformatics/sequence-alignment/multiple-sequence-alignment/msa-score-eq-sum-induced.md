# The SP score is the sum of the induced pairwise scores

Let $\sigma$ assign an integer
score to each pair of letters and let $g$ be an integer gap score. For every multiple alignment
$A$ of $k$ sequences, the sum-of-pairs score of $A$ equals the sum, over all pairs of rows
$i < j < k$, of the score of the pairwise alignment induced by $A$ on rows $i$ and $j$.
