# The sample has at most half the length, rounded up

For every list $xs$ (over any
type), the sample of $xs$ has length at most $\lfloor (|xs| + 1)/2 \rfloor$, half the length of
$xs$ rounded up: for an even length $2m$ the bound is $m$, and for an odd length $2m + 1$ it is
$m + 1$.
