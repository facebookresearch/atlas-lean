# Encoding a list of target values

The encoding of a list of target values as nested pairs
sends the empty list to the unit value and a list with head $w$ and tail $ws$ to the pair of $w$
and the encoding of $ws$. Thus $[w_0, \dots, w_{k-1}]$ is encoded as
$(w_0, (w_1, \dots (w_{k-1}, \mathsf{unit})))$.
