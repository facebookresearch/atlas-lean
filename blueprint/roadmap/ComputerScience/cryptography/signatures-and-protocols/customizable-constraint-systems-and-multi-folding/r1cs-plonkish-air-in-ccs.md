# R1CS is a degree-two CCS

Let an R1CS structure consist of matrices $A,B,C\in\mathbb{F}^{m\times m}$, each with at most $n=\Omega(m)$ nonzero entries, and let an instance $x\in\mathbb{F}^{\ell}$ ($m>\ell$) be satisfied by a witness $W\in\mathbb{F}^{m-\ell-1}$ iff $AZ\circ BZ=CZ$ for $Z=(W,x,1)$. Let $M_1,M_2,M_3\in\mathbb{F}^{m\times m}$ be $A,B,C$ with their columns permuted so that $M_jz$ equals the corresponding product with $Z$ for $z=(W,1,x)$. Then the CCS structure with these $m$ rows and $m$ columns, $t=3$, $q=2$, $d=2$, matrices $M_1,M_2,M_3$, multisets $S_1=\{1,2\}$, $S_2=\{3\}$ and constants $c_1=1$, $c_2=-1$ has at most $3n$ nonzero entries, and for every $x$ and $W$, $W$ satisfies the R1CS instance $x$ iff it satisfies the CCS instance $x$ in the matrix form $\sum_ic_i\cdot\bigcirc_{j\in S_i}M_jz=\mathbf{0}$. The CCS therefore has the same $m$ constraints and the same witness vector $W$ as the R1CS; for the arithmetized (multilinear) form of CCS the dimensions are padded to powers of two.

## Proof sketch

Permuting columns of a matrix together with the entries of the vector it multiplies does not change the product, so $M_1z=AZ$, $M_2z=BZ$ and $M_3z=CZ$. Hence $c_1(M_1z\circ M_2z)+c_2M_3z=AZ\circ BZ-CZ$, which is zero exactly when the R1CS equation holds.

## Depends on

- [Customizable constraint systems](customizable-constraint-system.md)
- [Rank-1 constraint systems](../relaxed-r1cs-folding-schemes/rank-one-constraint-system.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573, Definition 1 (CCS), Definition 22 (R1CS), and the proof of Lemma 3, which reduces R1CS to CCS.
