# Decomposable lookup tables

A table $\mathbf{T}\in\mathbb{F}^{N}$ indexed by $\{0,1\}^{\log N}$ is *$c$-decomposable* (with $k$ subtables) if there are tables $T_1,\dots,T_k$ of size $N^{1/c}$, each with a multilinear extension evaluable in $O(\log N)$ time, and a multilinear polynomial $g$ of total degree at most $k$ such that, writing an index $r=(r_1,\dots,r_c)$ as $c$ chunks of $\log N/c$ bits, $\mathbf{T}[r]=g\bigl(T_1[r_{i_1}],\dots,T_k[r_{i_k}]\bigr)$ for fixed chunk assignments $i_1,\dots,i_k\in\{1,\dots,c\}$.

## Depends on

- [Multilinear extension of a Boolean function](../../../../TheoryOfComputation/hierarchy-theorems-and-barriers/algebrization-barrier/multilinear-ext.md)

## Sources

- Srinath Setty, Justin Thaler, Riad Wahby, "Unlocking the Lookup Singularity with Lasso", EUROCRYPT (2024), IACR ePrint 2023/1216.
- Arasu Arun, Srinath Setty, Justin Thaler, "Jolt: SNARKs for Virtual Machines via Lookups", EUROCRYPT (2024), IACR ePrint 2023/1217.
