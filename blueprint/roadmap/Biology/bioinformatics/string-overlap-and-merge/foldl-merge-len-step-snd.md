# The tracked length is the merged length

For every list $\ell$ of strings and every string $a$, folding the [length-tracking step](merge-len-step.md) along $\ell$ from the pair $(a, |a|)$ ends with the length of the left fold of [merge](merge.md) along $\ell$ from $a$. The starting count must be $|a|$: from $([], 1)$ and the empty $\ell$ the count is $1$, although the merged string is empty.
