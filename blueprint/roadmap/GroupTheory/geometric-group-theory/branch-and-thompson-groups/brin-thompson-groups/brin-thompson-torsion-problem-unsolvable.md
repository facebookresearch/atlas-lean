# The Brin–Thompson groups nV with n at least 2 have unsolvable torsion problem

For every $n \ge 2$ the finitely presented group $nV$, which has solvable word problem, has unsolvable torsion problem: no algorithm decides whether a given element has finite order.

For every integer $n \ge 2$ and every finite generating set of the Brin–Thompson group $nV$, there is no algorithm that decides, given a word in the generators and their inverses, whether it represents an element of finite order in $nV$ (Theorem 1.1 of the source). The groups $nV$ are finitely presented with solvable word problem, so they are concrete finitely presented groups with solvable word problem and unsolvable torsion problem; the existence of such groups was first shown, without an explicit example, by Arzhantseva, Lafont and Minasyan. Thompson's groups $F$, $T$ and $V = 1V$ have solvable torsion problem.

## Depends on

- [Brin–Thompson group nV](brin-thompson-group.md)
- [Order problem and torsion problem of a finitely generated group](../../../presentations-and-decision-problems/conjugacy-order-and-power-problems/order-and-power-problems/order-problem.md)
- [Group](../../../group-basics/group.md)
- [Solvable word problem](../../../presentations-and-decision-problems/word-problem-for-groups/word-problem-solvable.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

Since $2V$ embeds in $nV$ for $n \ge 2$, it suffices to treat $2V$. A Turing machine is complete and reversible when its transition relation defines a bijection $F$ of the configuration space $Q \times \Sigma^{\mathbb{Z}}$; it is uniformly periodic when some power $F^m$ is the identity. Kari and Ollinger proved that uniform periodicity of complete reversible Turing machines is undecidable. The source shows that every complete reversible Turing machine is topologically conjugate to an effectively constructible element of $2V$ acting on $C^2$, with $F$ of finite order exactly when the element is; a solution of the torsion problem in $2V$ would therefore decide uniform periodicity.

## Sources

- J. Belk and C. Bleak, "Some undecidability results for asynchronous transducers and the Brin–Thompson group 2V", Transactions of the American Mathematical Society 369 (2017), no. 5, 3157–3172, https://doi.org/10.1090/tran/6963; arXiv:1405.0982v1 (Theorem 1.1, with the Kari–Ollinger theorem as Theorem 2.4, of arXiv:1405.0982v1).
