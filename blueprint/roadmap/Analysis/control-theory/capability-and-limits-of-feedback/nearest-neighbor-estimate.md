# Nearest-neighbor estimate from past transitions

Fix a positive time $t=n+1$ with $n\in\mathbb{N}$. Given real observations
$y_0,\ldots,y_t$ and past real controls $u_0,\ldots,u_{t-1}$, let $i_t$ be
the least index in $\{0,\ldots,t-1\}$ attaining the minimum of $|y_t-y_i|$
over that set. Equivalently, take the lexicographic minimum of the pairs
$(|y_t-y_i|, i)$: distance comes first, and the index distinguishes ties.
The set is nonempty because $t\ge 1$. Define

$$
\widehat f_t(y_t)=y_{i_t+1}-u_{i_t}.
$$

The observation history is indexed by `Fin (n + 2)` and the control history
by `Fin (n + 1)`. For a candidate index `i : Fin (n + 1)`, `i.castSucc`
indexes $y_i$, `i.succ` indexes $y_{i+1}$, and the last observation index
is $t$. In particular, $i_t+1\le t$: the estimate uses neither observations
after time $t$ nor controls at or after $t$. It requires no unknown plant
function as an input, and does not define a switching feedback law.

## Sources

- L. Guo, [*Exploring the capability and limits of the feedback mechanism*](https://arxiv.org/pdf/math/0305011v1),
  Proc. ICM 2002, Vol. III, arXiv:math/0305011v1, Remark 4.1, pp. 790–791. The
  least-index convention fixes a choice left unspecified in the source.
