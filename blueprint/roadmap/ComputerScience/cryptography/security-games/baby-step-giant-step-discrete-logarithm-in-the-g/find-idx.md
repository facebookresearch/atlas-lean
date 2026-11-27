# Index lookup in the baby table

Let $q > 1$. For a label $\mathit{cur}$, a list of labels $\mathit{tab}$ and a natural number $k$ labeling the head of the list, the lookup returns $\mathrm{some}(k + j)$ if the first occurrence of $\mathit{cur}$ in $\mathit{tab}$ is at zero-based index $j$, and $\mathrm{none}$ if $\mathit{cur}$ does not occur. Equality of labels is decidable equality. For example, the lookup of $\mathit{cur}$ in the one-entry list $[\mathit{cur}]$ with head label $5$ returns $\mathrm{some}\ 5$.
