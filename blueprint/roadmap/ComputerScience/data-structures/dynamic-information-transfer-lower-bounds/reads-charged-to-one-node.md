# Each cell read is charged to at most one tree node

In the information-transfer tree of any operation sequence, $\sum_v |\mathrm{IT}(v)|$ is at most the total number of cell reads performed during the sequence. Consequently, if every internal node $v$ at depth $d$ satisfies $|\mathrm{IT}(v)| \ge c \cdot |R_v| \cdot \beta_d$, then the total number of probes is at least $c\, m \sum_d \beta_d / 2$.

## Proof sketch

A read at time $t$ of a cell last written at time $s < t$ contributes to $\mathrm{IT}(v)$ only for $v$ the lowest common ancestor of the leaves $s$ and $t$, since $s$ must lie in the left and $t$ in the right subtree interval of $v$. Each read is therefore charged at most once. The nodes at a fixed depth have disjoint right intervals covering about half of the time axis, so their right-interval sizes sum to at least $m/2$, which gives the second claim.

## Depends on

- [Information transfer and the information-transfer tree](information-transfer-tree.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
