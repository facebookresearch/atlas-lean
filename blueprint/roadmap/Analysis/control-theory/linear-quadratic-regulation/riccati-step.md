# One step of the discrete Riccati recursion

For a state matrix $A$, input matrix $B$, stage costs $Q$ (state) and $R$ (input) and a next-stage cost matrix $P$, one step of the discrete linear-quadratic regulator Riccati recursion is

$$Q + A^\top P A - A^\top P B\,(R + B^\top P B)^{-1} B^\top P A.$$
