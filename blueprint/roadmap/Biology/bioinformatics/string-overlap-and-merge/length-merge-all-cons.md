# Length of the greedy merge of a nonempty list

For a string $s$ and a list $\ell$ of strings, the length of the [greedy merge](merge-all.md) of $s :: \ell$ equals the length of the left fold of [merge](merge.md) along $\ell$ from $\mathrm{merge}([], s)$.
