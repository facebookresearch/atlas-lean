# Semigroup presentations and the word problem

A semigroup presentation lists generators and defining relations between words; the semigroup it presents is the free semigroup modulo the congruence the relations generate, and its word problem asks whether two words represent the same element.

A *semigroup* is a set with an associative binary operation. For a set $A$, the *free semigroup* $A^+$ consists of the nonempty words over $A$ under concatenation. For pairs of words $u_i, v_i \in A^+$ ($i \in I$), the semigroup

$$
\mathrm{Sgp}\langle A \mid u_i = v_i \ (i \in I) \rangle = A^+ / \sigma
$$

is the quotient of $A^+$ by the smallest congruence $\sigma$ containing all pairs $(u_i, v_i)$; equivalently, two words are equal in it iff one can be transformed into the other by finitely many replacements of a factor $u_i$ by $v_i$ or of $v_i$ by $u_i$. The presentation is *finite* if $A$ and $I$ are finite, and a semigroup is *finitely presented* if it has a finite presentation. The *word problem* of a finitely presented semigroup $S = \mathrm{Sgp}\langle A \mid R \rangle$ asks, given two words $w, w' \in A^+$, whether $w = w'$ in $S$. Its decidability does not depend on the finite presentation chosen. Monoid presentations, over the free monoid $A^*$, are defined in the same way, and the word problem of a finite monoid presentation is the word problem of a Thue system.

## Depends on

- [The word problem of a Thue system](../../../TheoryOfComputation/undecidable-problems/string-rewriting-systems/thue-wp.md)

## Proof depends on

None.

## Expansion

Finitely presented semigroups and monoids are also called associative calculi or Thue systems; the *uniform* word problem takes the finite presentation as part of the input as well.

## Sources

- Bjorn Poonen, "Undecidable problems: a sampler", in *Interpreting Gödel: Critical Essays* (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, doi:[10.1017/CBO9780511756306.015](https://doi.org/10.1017/CBO9780511756306.015); read in arXiv:1204.0299v2 ([arXiv](https://arxiv.org/abs/1204.0299v2)), Section 6.2 (the word problem), section numbering of that version.
- Mark Sapir, "Minsky Machines and Algorithmic Problems", in *Fields of Logic and Computation II*, Lecture Notes in Computer Science 9300, Springer, 2015, pp. 273–292, doi:[10.1007/978-3-319-23534-9_17](https://doi.org/10.1007/978-3-319-23534-9_17); read in arXiv:1504.07736v1 ([arXiv](https://arxiv.org/abs/1504.07736v1)), whose numbering is used: Section 3 (semigroups given by generators and defining relations simulating Minsky machines) and Section 4.
