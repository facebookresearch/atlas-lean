# Rank–trace estimates for extracting distinct and simple zeros

For finite complex vectors $v_j$ of weights $m_j\ge0$, put $P=\sum_j m_j v_jv_j^*$. Let $Q$ be Hermitian with at most $b$ strictly positive eigenvalues. With $c>0$ write $g_c(x)=x^2-cx-(\max\{x-c,0\})^2$ for $x\ge0$.
The multiplicity-sensitive rank–trace estimate bounds $c\operatorname{tr}P+\sum_jg_c(m_j\|v_j\|^2)+2c\operatorname{tr}Q-c^2b$ from above by $\|P+Q\|_F^2$, using real traces. In the zero-window application, separate the on-line atoms in $P$ (with integer orders) and off-line reflection pairs in $Q$. Count orders in the denominator but count each eligible atom only once in the numerator. The mass from outside the target window must be bounded before applying the fixed-window estimate.

## Depends on

- [Count with multiplicity](count-with-multiplicity.md)
- [Simple distinct points on the line](count-simple-on-line.md)

## Expansion

Build the Gram block decomposition and bound its outside-window error. Track reflection pairs, positive index, and the dependence on each individual integral order. The source uses different substitutions in the certificate to extract all on-line points, simple on-line points, or all distinct points; do not replace the multiplicity-sensitive estimate by a distinct-rank count.

## Sources

- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/ZeroSide/RankTraceMult.lean#L275-L286).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/Assembly/Certificate.lean#L22-L63).
- Anthropic, [formalized argument](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/Zeta23/Assembly/CertificateC3.lean#L22-L48).
