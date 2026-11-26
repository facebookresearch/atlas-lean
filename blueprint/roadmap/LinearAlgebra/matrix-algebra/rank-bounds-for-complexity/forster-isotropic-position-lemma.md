# Forster's isotropic-position lemma

Let $u_1,\dots,u_m\in\mathbb{R}^d$ be in general position (every $d$ of them are linearly independent), $m\ge d$. Then there is an invertible linear map $B$ such that the normalized vectors $w_x=Bu_x/\|Bu_x\|$ are in isotropic position: $\sum_{x=1}^mw_xw_x^{T}=\frac md I_d$. Consequently (Forster's theorem) every sign matrix $S\in\{\pm1\}^{m\times n}$ has sign rank at least $\sqrt{mn}/\|S\|$.

## Proof sketch

Choose probability weights $p_x$ maximizing $\log\det\bigl(\sum_xp_xu_xu_x^{T}\bigr)$; general position keeps the maximizer in the interior of the simplex, and the stationarity conditions give $u_x^{T}A^{-1}u_x=d$ for $A=\sum_xp_xu_xu_x^{T}$, so $B=A^{-1/2}$ puts the normalized vectors in isotropic position.

## Depends on

- [Subadditivity of the rank](../../../Analysis/approximation-theory/low-rank-matrix-recovery/rank-sub-le.md)

## Sources

- Jürgen Forster, "A Linear Lower Bound on the Unbounded Error Probabilistic Communication Complexity", Journal of Computer and System Sciences, 2002.
- Noga Alon, Shay Moran, Amir Yehudayoff, "Sign Rank versus VC Dimension", 2016.
