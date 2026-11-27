# Forster's isotropic-position lemma

Let $u_1,\dots,u_m\in\mathbb{R}^d$ be in general position (every $d$ of them are linearly independent), $m\ge d$. Then there is an invertible linear map $B$ such that the normalized vectors $w_x=Bu_x/\|Bu_x\|$ are in isotropic position: $\sum_{x=1}^mw_xw_x^{T}=\frac md I_d$. Consequently (Forster's theorem) every sign matrix $S\in\{\pm1\}^{m\times n}$ has sign rank at least $\sqrt{mn}/\|S\|$.

## Proof sketch

Choose weights $c_x = e^{t_x}$ maximizing $\log\det\bigl(\sum_x c_x u_xu_x^{T}\bigr)$ subject to $\sum_x t_x = 0$; general position makes the maximum attained, and stationarity gives $c_x\,u_x^{T}A^{-1}u_x=d/m$ for $A=\sum_x c_x u_xu_x^{T}$, so with $B=A^{-1/2}$, $\sum_x w_xw_x^T = \frac{m}{d}\sum_x c_x Bu_xu_x^TB = \frac md I_d$.

## Depends on

- [Subadditivity of the rank](../../../Analysis/approximation-theory/low-rank-matrix-recovery/rank-sub-le.md)

## Sources

- Jürgen Forster, "A Linear Lower Bound on the Unbounded Error Probabilistic Communication Complexity", Journal of Computer and System Sciences, 2002.
- Noga Alon, Shay Moran, Amir Yehudayoff, "Sign Rank versus VC Dimension", 29th Conference on Learning Theory (COLT 2016), 2016.
