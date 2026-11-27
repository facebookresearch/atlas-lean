# The cell-mean coefficients solve the normal equations

For a finite sample with binary indicators $D_i$ and $T_i$ (for example treated group and post period) and responses $y_i$, let $m_{ab}$ be the mean of $y$ over the cell $\{i : D_i = a, T_i = b\}$ (with $0$ for an empty cell), and let the cell-mean coefficients be $c = \big(m_{00},\ m_{10} - m_{00},\ m_{01} - m_{00},\ (m_{11} - m_{10}) - (m_{01} - m_{00})\big)$. Write $W$ for the saturated design matrix with rows $(1, D_i, T_i, D_iT_i)$. Then $W^\top Wc = W^\top y$ for every sample, empty cells included.
