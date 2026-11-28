# The saturated fit reproduces the cell means

For a finite sample with binary indicators $D_i$ and $T_i$ (for example treated group and post period) and responses $y_i$, let $m_{ab}$ be the mean of $y$ over the cell $\{i : D_i = a, T_i = b\}$ (with $0$ for an empty cell), and let the cell-mean coefficients be $c = \big(m_{00},\ m_{10} - m_{00},\ m_{01} - m_{00},\ (m_{11} - m_{10}) - (m_{01} - m_{00})\big)$. Write $W$ for the saturated design matrix with rows $(1, D_i, T_i, D_iT_i)$. Then $(Wc)_i = m_{D_iT_i}$ for every $i$: the fitted value of each observation is the mean of its own cell.
