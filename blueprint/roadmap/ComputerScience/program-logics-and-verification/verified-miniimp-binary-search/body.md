# Loop body of binary search

For an array $xs$ of natural numbers and a natural-number key, the loop body of binary search is the MiniImp command

$$\mathit{mid} := \mathit{lo} + (\mathit{hi} - \mathit{lo}) / 2;\quad \mathit{value} := xs[\mathit{mid}];\quad \mathbf{if}\ \mathit{value} < \mathit{key}\ \mathbf{then}\ \mathit{lo} := \mathit{mid} + 1\ \mathbf{else}\ \mathit{hi} := \mathit{mid},$$

with truncated subtraction and floor division on natural numbers. The read of $xs[\mathit{mid}]$ is bounds-checked: an index outside the array has no execution. On equality, $\mathit{value} = \mathit{key}$, the else branch sets $\mathit{hi} := \mathit{mid}$: on the array $[5]$ with key $5$, from $\mathit{lo} = 0$ and $\mathit{hi} = 1$, the body sets $\mathit{hi} := 0$. On an array sorted in nondecreasing order, the full program therefore returns the first index whose entry is at least the key, or the array size if no such entry exists ([specification](big-step-spec.md)). On an unsorted array it need not: on $[5, 0, 5]$ with key $5$, the first iteration reads $0$ and sets $\mathit{lo} := 2$, the second reads $5$ and sets $\mathit{hi} := 2$, and the result is $2$ although index $0$ qualifies.
