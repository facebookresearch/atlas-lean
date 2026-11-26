# The best local action of a specification

For predicates $p_1, p_2$ over a [separation algebra](separation-algebras.md) $\Sigma$, define $\mathrm{bla}[p_1, p_2] : \Sigma \to P(\Sigma)^\top$ by

$$\mathrm{bla}[p_1, p_2]\,(\sigma) = \bigsqcap \{ p_2 \ast \{\sigma_0\} : \sigma = \sigma_0 \bullet \sigma_1,\ \sigma_1 \in p_1 \},$$

the meet being taken in $P(\Sigma)^\top$, so that the value is $\top$ when $\sigma$ has no substate in $p_1$. Then $f = \mathrm{bla}[p_1, p_2]$ is a [local action](local-actions.md), it satisfies $\langle\!\langle p_1 \rangle\!\rangle\, f\, \langle\!\langle p_2 \rangle\!\rangle$, and every local action $t$ with $\langle\!\langle p_1 \rangle\!\rangle\, t\, \langle\!\langle p_2 \rangle\!\rangle$ satisfies $t \sqsubseteq f$. In the heap model, disposal $\mathrm{free}(l) = \mathrm{bla}[l \mapsto -, \mathrm{emp}]$ is a best local action and allocation is a join of best local actions; and if $p$ is [precise](precise-predicates.md), $\mathrm{bla}[p, \mathrm{emp}]$ removes from a state its unique substate in $p$.

## Depends on

- [Local actions](local-actions.md)

## Proof depends on

- [Precise predicates distribute separating conjunction over intersections](precise-predicates-distribute-over-meets.md)

## Sources

- C. Calcagno, P. W. O'Hearn and H. Yang, "Local action and abstract separation logic", *Proceedings of the 22nd Annual IEEE Symposium on Logic in Computer Science (LICS 2007)*, IEEE, 2007; extended version of April 13, 2007, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/asl-long.pdf>, Section 3.2, Definition 10, Lemma 11 and Lemma 13.
