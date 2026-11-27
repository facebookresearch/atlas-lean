# Length of a merge fold, one step

For strings $s$, an accumulator $a$ and a list $\ell$ of strings, the length of the left fold of
the overlap merge along $s :: \ell$ starting from $a$ equals the length of the fold along $\ell$
starting from the merge of $a$ and $s$.
