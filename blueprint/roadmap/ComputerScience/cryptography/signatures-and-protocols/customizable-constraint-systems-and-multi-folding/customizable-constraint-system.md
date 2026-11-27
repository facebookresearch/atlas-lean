# Customizable constraint systems

Fix size bounds $m,n,N,\ell,t,q,d\in\mathbb{N}$ with $n>\ell$, where $m$ and $n$ are powers of two, and let $s=\log m$ and $s'=\log n$. A *customizable constraint system (CCS) structure* consists of sparse multilinear polynomials $\widetilde{M}_1,\dots,\widetilde{M}_t$ in $s+s'$ variables that are nonzero in at most $N=\Omega(m)$ points of $\{0,1\}^{s}\times\{0,1\}^{s'}$, multisets $S_1,\dots,S_q$ with elements in $\{1,\dots,t\}$ and each of cardinality at most $d$, and constants $c_1,\dots,c_q\in\mathbb{F}$. An instance is a public input and output vector $x\in\mathbb{F}^{\ell}$, and a witness is a multilinear polynomial $\widetilde{w}$ in $s'-1$ variables. The triple is satisfying iff, for every $a\in\{0,1\}^{s}$,

$$
\sum_{i=1}^{q}c_i\prod_{j\in S_i}\Bigl(\sum_{y\in\{0,1\}^{s'}}\widetilde{M}_j(a,y)\,\widetilde{z}(y)\Bigr)=0,
$$

where $\widetilde{z}$ is the $s'$-variate multilinear polynomial that agrees with the vector $(w,1,x)$ on $\{0,1\}^{s'}$. Writing $M_j\in\mathbb{F}^{m\times n}$ for the matrix of values of $\widetilde{M}_j$ on the hypercube and $z\in\mathbb{F}^{n}$ for the values of $\widetilde{z}$, the condition is the matrix identity $\sum_{i=1}^{q}c_i\cdot\bigcirc_{j\in S_i}M_jz=\mathbf{0}$, where $\bigcirc$ is the iterated Hadamard product. The bound $d$ is the *degree* of the system.

## Depends on

- [Rank-1 constraint systems](../relaxed-r1cs-folding-schemes/rank-one-constraint-system.md)
- [Multilinear extension of a Boolean function](../../../../TheoryOfComputation/hierarchy-theorems-and-barriers/algebrization-barrier/multilinear-ext.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573, Definition 1 (the arithmetized form of the CCS relation).
