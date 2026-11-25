# Upwind step preserves nonnegativity

On a periodic grid of $n \ge 1$ cells with cross-section area $A > 0$ and spacing $\Delta x > 0$, let $\Delta t \ge 0$ and velocity $v \ge 0$ satisfy the CFL condition $v\,\Delta t/\Delta x \le 1$. If $c_i \ge 0$ for all cells and $c^{\text{next}}$ is the conservative update of $c$ with the upwind face flux, then $c^{\text{next}}_i \ge 0$ for all cells.
