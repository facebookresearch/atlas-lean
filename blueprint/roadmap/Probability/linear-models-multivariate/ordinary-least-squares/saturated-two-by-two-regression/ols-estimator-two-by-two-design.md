# Least squares on the saturated two-by-two design

For a finite sample with binary indicators $D_i$ and $T_i$ (for example treated group and post period) and responses $y_i$, let $m_{ab}$ be the mean of $y$ over the cell $\{i : D_i = a, T_i = b\}$ (with $0$ for an empty cell), and let the cell-mean coefficients be $c = \big(m_{00},\ m_{10} - m_{00},\ m_{01} - m_{00},\ (m_{11} - m_{10}) - (m_{01} - m_{00})\big)$. Write $W$ for the saturated design matrix with rows $(1, D_i, T_i, D_iT_i)$. If all four cells are nonempty, the least-squares estimate $(W^\top W)^{-1}W^\top y$ equals $c$.

## Sources

- J. D. Angrist and J.-S. Pischke, *Mostly Harmless Econometrics*, Princeton University Press (2009), §3.1.4 and §5.2.1.
