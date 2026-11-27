# Global stability parameter equals the reciprocal list replicability number

For every concept class $H$,

$$
\rho(H) = \frac{1}{\mathrm{LR}(H)} \quad \text{and} \quad \rho_{\mathrm{agn}}(H) = \frac{1}{\mathrm{LR}_{\mathrm{agn}}(H)},
$$

where the list numbers take values in $\{1, 2, \dots\} \cup \{\infty\}$ and $1/\infty = 0$. Thus $\rho(H) = 0$ exactly when $\mathrm{LR}(H) = \infty$, as for a class of infinite VC dimension, and likewise in the agnostic case; no product $0 \cdot \infty$ is involved. In particular global stability parameters are always reciprocals of integers or zero, a class is globally stable exactly when it is list replicable, and global stability can be weakly boosted (for instance $\rho(H) \ge 0.31$ implies $\rho(H) \ge 1/3$). The conversions between the two kinds of learners are algorithmic.

## Proof sketch

A list replicable learner with list size $L$ outputs one of $L$ hypotheses with probability close to one, so one of them is output with probability at least about $1/L$, which is global stability. Conversely, given an $\eta$-globally stable learner, run it on many independent samples, estimate the output frequencies, and output a canonical hypothesis among those whose frequency exceeds a randomly chosen threshold below $\eta$; at most $\lfloor 1/\eta \rfloor$ hypotheses can be that frequent, which bounds the list size.

## Depends on

- [Global stability and list replicability of learning rules](global-stability-and-list-replicability.md)

## Sources

- Z. Chase, S. Moran, A. Yehudayoff, "Replicability and Stability in Learning", FOCS (2023), arXiv:2304.03757.
- Z. Chase, B. Chornomaz, S. Moran, A. Yehudayoff, "Local Borsuk-Ulam, Stability, and Replicability", STOC (2024), arXiv:2311.01599.
