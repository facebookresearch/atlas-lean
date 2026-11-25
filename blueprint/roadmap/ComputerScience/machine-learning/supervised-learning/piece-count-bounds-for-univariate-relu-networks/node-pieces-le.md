# Node pieces LE

Per-node bound for positive widths: the output of node `j` after `i`
layers has at most `2 ^ i` times the product of widths over layers `1` to
`i - 1` pieces. Only the traversed layers are constrained, so widths after
layer `i` may be zero (finite-network encodings); positivity of the traversed
widths is still necessary (a zero traversed width collapses the product bound).
