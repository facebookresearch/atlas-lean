# Gotoh value with no open gap run

Given a substitution score $\sigma$, a gap-open score
$g_o$ and a gap-extend score $g_e$, this is the value of the Gotoh dynamic program on sequences
$x$ and $y$ when no gap run is open (the previous column was a match, or there is no previous
column): the best affine-gap score of an alignment of $x$ and $y$, where a match column pairing
$a$ with $b$ scores $\sigma(a, b)$ and a gap column scores $g_e$ if it continues a run of gaps in
the same sequence and $g_o$ otherwise.

It is a continuation value, not an endpoint-restricted matrix: the first column may be a match
or either gap.
