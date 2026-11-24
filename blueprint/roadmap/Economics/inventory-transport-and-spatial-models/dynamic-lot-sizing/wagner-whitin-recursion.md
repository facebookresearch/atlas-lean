# The Wagner–Whitin dynamic lot-sizing recursion

Consider a finite horizon $1, \dots, T$ with deterministic demands $d_t \ge 0$, uncapacitated orders received immediately (zero lead time), no backlogging, zero initial and terminal stock and no salvage, a setup cost $K_t \ge 0$ charged exactly when the order in period $t$ is positive, linear purchase costs $c_tq_t$ and holding costs $h_t \ge 0$ on end-of-period stock. Some optimal plan orders only when entering stock is zero, each order covering the demand of a consecutive block of periods. Consequently, with $\mathrm{cost}(i, j)$ the cost of ordering $d_i + \dots + d_j$ in period $i$ and holding it until used (setup charged only if that sum is positive), $F(0) = 0$ and $F(j) = \min_{1 \le i \le j}(F(i - 1) + \mathrm{cost}(i, j))$ give the optimal cost $F(T)$, and the minimizing indices reconstruct an optimal plan.

## Expansion

A sound expansion specifies the following prerequisites and links their statements.

- Zero-inventory-ordering property: some optimal plan orders only when entering stock is zero (exchange argument).
- A primary source that states this result in the form given here is to be located and checked before the statement is relied on.
