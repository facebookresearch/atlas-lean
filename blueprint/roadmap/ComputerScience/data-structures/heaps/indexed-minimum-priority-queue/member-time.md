# Membership costs one position read

Let $q$ be an indexed min queue over a linear
order $W$ with identities in $\{0, \dots, n-1\}$ and let $v$ be an identity. The cost of the
membership test for $v$ in $q$, counted in five event classes (comparisons, swaps,
position-vector reads, position-vector writes, and entry appends, pops or replacements), is
exactly one position-vector read and no event of any other class.
