# Picard recursion of the signature series

Let $\iota$ be finite, $E$ a real Banach space, $A_i : E \to E$ continuous linear maps, and let
the velocity of $X$ be continuous. Write $A_w = A_{i_k} \circ \cdots \circ A_{i_1}$ for a word
$w = i_1 \cdots i_k$ and
$y^{(n)}_t = \sum_{|w| \le n} S(X)^w_{s,t}\, A_w y_0$ for the truncated signature series. Then

$$y^{(n+1)}_t = y_0 + \int_s^t \sum_i v^i(r)\, A_i\, y^{(n)}_r \, dr ,$$

the Picard recursion of the linear controlled equation $dy_t = \sum_i A_i y_t\, dX^i_t$,
$y_s = y_0$ (and $y^{(0)} = y_0$). So the Picard iterates of a linear controlled equation are
exactly the truncations of its signature series.

## Sources

- T. Lyons, *Rough paths, signatures and the modelling of functions on streams*, Proc. ICM 2014,
  arXiv:1405.4537, §4.2 ("By iterating using Picard iteration one obtains", equation (1)).
- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, §1.2.3 (Picard iteration for linear vector fields).
