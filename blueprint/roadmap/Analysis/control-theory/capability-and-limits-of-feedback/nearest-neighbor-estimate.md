# Nearest-neighbor estimate from past transitions

Fix an integer $t\ge 1$. Given real observations $y_0,\ldots,y_t$ and
past real inputs $u_0,\ldots,u_{t-1}$, let $i_t$ be the least index in
$\{0,\ldots,t-1\}$ attaining the minimum of $|y_t-y_i|$ over that set.
The set is finite and nonempty; taking the least minimizing index fixes a
single choice even if distances tie or observations repeat. Define

$$
\widehat f_t(y_t)=y_{i_t+1}-u_{i_t}.
$$

The next observation associated with the selected past index is already
available because $i_t+1\le t$. The estimate uses no observation after time
$t$ and does not require the unknown plant function as an input. It is not
used at time $0$, when there is no past transition.

## Sources

- L. Guo, [*Exploring the capability and limits of the feedback mechanism*](https://arxiv.org/pdf/math/0305011v1),
  Proc. ICM 2002, Vol. III, arXiv:math/0305011v1, Remark 4.1, p. 7. The
  least-index convention fixes a choice left unspecified in the source.
