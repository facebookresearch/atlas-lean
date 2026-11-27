# Solving systems of equations is undecidable in Z wr Z

No algorithm decides whether a finite system of equations with constants has a solution in the wreath product $\mathbb{Z} \wr \mathbb{Z}$, answering a problem of Kharlampovich, López and Miasnikov.

An equation with constants over a group $G$ is $w(x_1, \dots, x_k) = 1$ with $w$ a word in variables $x_i$ and elements of $G$; a solution assigns elements of $G$ to the variables. Solving systems of equations is undecidable in $\mathbb{Z} \wr \mathbb{Z}$ (Theorem 1.3 of the source), answering a problem of Kharlampovich, López and Miasnikov; a fortiori the existential theory of $\mathbb{Z} \wr \mathbb{Z}$ with constants is undecidable.

The same method gives a finitely generated abelian-by-cyclic group $\mathcal{A} \rtimes \mathbb{Z}$ and elements $h_1, \dots, h_m$ such that it is undecidable, given $h_0$, whether there are $g_0, \dots, g_m$ with $(g_0 h_0 g_0^{-1})(g_1 h_1 g_1^{-1}) \cdots (g_m h_m g_m^{-1}) = 1$ (Theorem 1.4); so solving a single quadratic (spherical) equation is undecidable in this group, answering a problem of Lysenok and Ushakov.

By contrast, systems of quadratic equations are decidable in $A \wr \mathbb{Z}$ and in $\mathrm{BS}(1, p)$ (results recalled in the source).

## Depends on

- [Group](../../group-basics/group.md)
- [Restricted wreath product](../../soluble-finite-groups/solubility-nilpotency-and-subnormality/restricted-wreath.md)
- [Abelian group](../../group-basics/abelian-group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

Both results reduce from the undecidability of linear equations with monomial constraints over $\mathbb{Z}[X^{\pm}]$: there are a finitely presented module $\mathcal{A}$ and fixed $f_1, \dots, f_n$ for which solvability of $X^{z_1} f_1 + \cdots + X^{z_n} f_n = f_0$ in integers is undecidable (Theorem 1.1, from Hilbert's tenth problem). In $\mathbb{Z} \wr \mathbb{Z}$ the base group is $\mathbb{Z}[X^{\pm}]$, and conjugation by powers of the generator realizes the monomials; for the abelian-by-cyclic group, conjugates $g_i h_i g_i^{-1}$ do the same.

## Sources

- R. Dong, "Linear equations with monomial constraints and decision problems in abelian-by-cyclic groups", in Proceedings of the 2025 Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2025), SIAM (2025), 1892–1908, https://doi.org/10.1137/1.9781611978322.59; read in arXiv:2406.08480v3, whose numbering is used here (Theorems 1.1, 1.3 and 1.4 of arXiv:2406.08480v3).
