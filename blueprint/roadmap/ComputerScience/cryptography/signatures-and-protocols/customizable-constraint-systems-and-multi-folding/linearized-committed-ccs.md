# Linearized committed CCS instances

Let $s=\log m$ and $s'=\log n$. A *committed CCS (CCCS) instance* is $(C,x)$ where $C$ commits to the multilinear extension $\widetilde{w}$ of the witness. A *linearized committed CCS (LCCCS) instance* is $(C,u,x,r,v_1,\dots,v_t)$ with $u\in\mathbb{F}$, $r\in\mathbb{F}^{s}$, $v_j\in\mathbb{F}$; a witness $\widetilde{w}$ satisfies it iff $C$ opens to $\widetilde{w}$ and, with $\widetilde{z}$ the multilinear extension of $z=(w,u,x)$,

$$
v_j=\sum_{y\in\{0,1\}^{s'}}\widetilde{M}_j(r,y)\,\widetilde{z}(y)\quad\text{for }j=1,\dots,t.
$$

Thus an LCCCS instance asserts linear (degree-one) claims about the matrix-vector products at a random row point, which are closed under random linear combination, while the degree-$d$ CCS constraint is captured by a CCCS instance.

## Depends on

- [Customizable constraint systems](customizable-constraint-system.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Multilinear extension of a Boolean function](../../../../TheoryOfComputation/hierarchy-theorems-and-barriers/algebrization-barrier/multilinear-ext.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573.
