# Customizable constraint systems

A *customizable constraint system (CCS) structure* is a tuple $(m,n,N,\ell,t,q,d,M_1,\dots,M_t,S_1,\dots,S_q,c_1,\dots,c_q)$ with matrices $M_j\in\mathbb{F}^{m\times n}$ having at most $N$ nonzero entries in total, multisets $S_i\subseteq\{1,\dots,t\}$ each of size at most $d$, and constants $c_i\in\mathbb{F}$. An instance $x\in\mathbb{F}^{\ell}$ with witness $w\in\mathbb{F}^{n-\ell-1}$ is satisfying iff, for $z=(w,1,x)$,

$$
\sum_{i=1}^{q}c_i\cdot\bigcirc_{j\in S_i}M_j z=\mathbf{0},
$$

where $\bigcirc$ is the iterated Hadamard product. The *degree* of the system is $d$.

## Depends on

- [Rank-1 constraint systems](../relaxed-r1cs-folding-schemes/rank-one-constraint-system.md)

## Sources

- Srinath Setty, Justin Thaler, Riad Wahby, "Customizable Constraint Systems for Succinct Arguments", IACR ePrint 2023/552 (2023).
- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573.
