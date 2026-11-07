# The sum-of-pairs score is bounded by the pairwise optima

Fix a score
$\sigma(a, b) \in \mathbb{Z}$ for each pair of letters $a, b$ of an alphabet $\alpha$ and a gap
score $g \in \mathbb{Z}$. Let $s_0, \dots, s_{k-1}$ be sequences over $\alpha$ and let $A$ be a
valid multiple alignment of them: no column of $A$ consists only of gaps, and deleting the gaps
from row $i$ of $A$ leaves $s_i$. Then the sum-of-pairs score of $A$ under $\sigma$ and $g$ is at
most $\sum_{0 \le i < j < k} \mathrm{NW}(s_i, s_j)$, where $\mathrm{NW}(s_i, s_j)$ is the optimal
global (Needleman–Wunsch) alignment score of $s_i$ and $s_j$ under $\sigma$ and $g$.
