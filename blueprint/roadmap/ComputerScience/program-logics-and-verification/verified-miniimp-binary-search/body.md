# Loop body of binary search

For an array $xs$ of natural numbers and a natural-number key, the loop body of binary search is the MiniImp command

$$\mathit{mid} := \mathit{lo} + (\mathit{hi} - \mathit{lo}) / 2;\quad \mathit{value} := xs[\mathit{mid}];\quad \mathbf{if}\ \mathit{value} < \mathit{key}\ \mathbf{then}\ \mathit{lo} := \mathit{mid} + 1\ \mathbf{else}\ \mathit{hi} := \mathit{mid},$$

with truncated subtraction and floor division on natural numbers. The read of $xs[\mathit{mid}]$ is bounds-checked: an index outside the array has no execution. On equality, $\mathit{value} = \mathit{key}$, the else branch sets $\mathit{hi} := \mathit{mid}$, so the search finds the first index whose entry is at least the key: on the array $[5]$ with key $5$, from $\mathit{lo} = 0$ and $\mathit{hi} = 1$, the body sets $\mathit{hi} := 0$.
