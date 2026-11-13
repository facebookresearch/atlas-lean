# Sorting edges by weight and input position

Sorting a list of validated edges is merge
sort with the comparison $(w, i) \preceq (w', i')$ if $w < w'$, or $w = w'$ and $i \le i'$, applied
to the pairs (weight, input position) of the edges.
