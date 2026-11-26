# Information transfer and the information-transfer tree

Fix a sequence of operations $o_1, \dots, o_m$ served by a dynamic cell-probe structure. For two adjacent time intervals $I_1 = [a, b]$ and $I_2 = [b+1, c]$, the *information transfer* $\mathrm{IT}(I_1, I_2)$ is the set of cells that are read during $I_2$ and whose most recent write before that read occurred during $I_1$. The *information-transfer tree* is a balanced binary tree whose leaves are the times $1, \dots, m$ in order; at each internal node $v$ with left subtree interval $L_v$ and right subtree interval $R_v$ it records $\mathrm{IT}(v) = \mathrm{IT}(L_v, R_v)$.

## Depends on

- [Amortized update and query cost of a dynamic cell-probe structure](amortized-cell-probe-costs.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
