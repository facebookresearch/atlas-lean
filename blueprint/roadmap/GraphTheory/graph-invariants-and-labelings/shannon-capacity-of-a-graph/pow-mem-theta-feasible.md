# Feasible values multiply along strong powers

Let $H$ be a graph on words $V^k$ such that any two distinct words that are not adjacent in $H$ differ, at some position $i$, in two distinct vertices $x_i \ne y_i$ that are not adjacent in $G$. The [strong power](strong-power.md) $G^{\boxtimes k}$ has this property, and so has every graph on $V^k$ with more edges. If $t$ is a [feasible value](../theta-function-of-a-graph/theta-feasible.md) of the theta program for $G$, witnessed by an orthogonal labeling $a$ and a handle $c$, then $t^k$ is a feasible value for $H$: the words get the [tensor products](tensor-vec.md) $a_{x_0} \otimes \dots \otimes a_{x_{k-1}}$ and the handle is $c \otimes \dots \otimes c$. By the [factorisation of inner products](inner-tensor-vec.md), two distinct non-adjacent words get orthogonal vectors, the handle is nonzero, and the cost of a word is the product of the costs of its letters, so $1 \le \prod_i t\, \mathrm{cost}_c(a_{x_i}) = t^k\, \mathrm{cost}$.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, §20, Lemma (eq. (20.5)) and its proof, eqs. (20.6)-(20.8), for two factors.
