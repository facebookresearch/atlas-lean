# Knapsack is undecidable for wreath products over the Heisenberg group

For every non-trivial group $G$, the knapsack problem for the restricted wreath product $G \wr H_3(\mathbb{Z})$ over the discrete Heisenberg group is undecidable, although the knapsack problem for $H_3(\mathbb{Z})$ itself is decidable.

Let $H_3(\mathbb{Z})$ be the discrete Heisenberg group of upper unitriangular $3 \times 3$ integer matrices, and for a group $G$ let $G \wr H_3(\mathbb{Z})$ be the restricted wreath product, the semidirect product of the finitely supported functions $H_3(\mathbb{Z}) \to G$ with $H_3(\mathbb{Z})$ acting by translation. For every finitely generated non-trivial group $G$, the knapsack problem $\mathrm{KP}(G \wr H_3(\mathbb{Z}))$, with exponents in the natural numbers, is undecidable (Theorem 3.3 of the source).

## Depends on

- [Knapsack problem for a finitely generated group](knapsack-problem-for-a-group.md)
- [Group](../../../group-basics/group.md)
- [Restricted wreath product](../../../soluble-finite-groups/solubility-nilpotency-and-subnormality/restricted-wreath.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)

## Expansion

The main result of the source characterizes decidability of $\mathrm{KP}(G \wr H)$ in terms of an intersection knapsack problem over $H$. For $H = H_3(\mathbb{Z})$, the source shows that the positive intersection knapsack problem $\mathrm{KP}^+(H_3(\mathbb{Z}))$ is undecidable (in the section on applications), by encoding integer polynomial equations through the quadratic behavior of products of powers in the Heisenberg group, and the characterization transfers undecidability to $G \wr H_3(\mathbb{Z})$. Earlier, Ganardi, König, Lohrey and Zetzsche had shown undecidability for $G \wr (H_3(\mathbb{Z}) \times \mathbb{Z}^\ell)$ for some $\ell$; by König, Lohrey and Zetzsche, $\mathrm{KP}(H_3(\mathbb{Z}))$ is decidable.

## Sources

- P. Bergsträßer, M. Ganardi and G. Zetzsche, "A characterization of wreath products where knapsack is decidable", 38th International Symposium on Theoretical Aspects of Computer Science (STACS 2021), Leibniz International Proceedings in Informatics (LIPIcs) 187 (2021), article 11, https://doi.org/10.4230/LIPIcs.STACS.2021.11; read in arXiv:2101.06132v1 (Theorem 3.3 of arXiv:2101.06132v1, with the undecidability of $\mathrm{KP}^+(H_3(\mathbb{Z}))$ proved in its section "Applications").
