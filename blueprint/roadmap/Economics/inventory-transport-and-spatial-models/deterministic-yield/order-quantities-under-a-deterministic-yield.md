# Order quantities under a deterministic yield

Suppose each raw unit ordered yields $y \in (0, 1]$ good units, so an order of $r \ge 0$ raw units delivers $q = y r$ good units.
Minimizing a cost $C(q)$ of the delivered quantity over raw orders is then the same problem, with raw optimum $q^*/y$.

- For the economic order quantity with constant good-unit demand rate $d > 0$, setup cost $K > 0$ and holding cost $h > 0$, the
  average cost $C(q) = K d/q + h q/2$ on $q > 0$ is minimized at $q^* = \sqrt{2 K d/h}$, so the raw order is $q^*/y$. With
  exactly one of $K,h$ zero and the other positive there is no finite optimum on $q>0$: the infimum is approached as $q\downarrow0$
  if $K=0$, or as $q\to\infty$ if $h=0$. If both $K=h=0$, the cost is identically zero and every $q>0$ is optimal.
- For a newsvendor with demand $D \in \{0, d\}$, $d > 0$, $P(D = d) = p \in [0, 1]$, shortage cost $c_u > 0$ and overage cost
  $c_o > 0$, the expected cost $E[c_u (D - q)_+ + c_o (q - D)_+]$ over good quantities $q \ge 0$ is minimized at $q = 0$ if
  $p < c_o/(c_u + c_o)$, at $q = d$ if $p > c_o/(c_u + c_o)$, and at every $q \in [0, d]$ at equality; the raw order is $q/y$.
  At the atoms of this demand law the optimum is described by left and right distribution-function inequalities, not by a
  continuous quantile equation.

## Depends on

## Proof depends on

## Expansion

Link the economic-order-quantity and critical-fractile newsvendor results once their pages are in the graph, and state this page
as their instance under a deterministic yield.

## Sources

- F. W. Harris, How many parts to make at once, *Factory, The Magazine of Management* 10 (1913) 135–136.
- K. J. Arrow, T. Harris and J. Marschak, Optimal inventory policy, *Econometrica* 19 (1951) 250–272.
