# Iterated second projections of an encoded environment

Let $\rho$ be a list of target
values, $e$ a target term and $ws = [w_0, \dots, w_{m-1}]$ a list of target values, and suppose
$e$ evaluates in $\rho$ to the encoding of $ws$, the nested pairs
$(w_0, (w_1, \dots (w_{m-1}, \mathsf{unit})\dots))$. Then for every natural number $k \le m$, the
term obtained by applying the second projection $k$ times to $e$ evaluates in $\rho$ to the
encoding of $[w_k, \dots, w_{m-1}]$, the list $ws$ with its first $k$ entries dropped.
