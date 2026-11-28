# Some finitely presented group has unsolvable conjugacy problem

There is a finitely presented group for which no algorithm decides, given two words in its generators, whether they represent conjugate elements. Novikov published this before his theorem on the word problem, with a simpler proof.

Let $G$ be a group given by a finite presentation with generators $x_1, \dots, x_n$. The *conjugacy problem* for $G$ asks, given two words $w_1, w_2$ in $x_1^{\pm 1}, \dots, x_n^{\pm 1}$, whether the elements they represent are conjugate in $G$, that is, whether $w_1 = g w_2 g^{-1}$ in $G$ for some $g \in G$.

**Theorem (Novikov).** There is a finitely presented group whose conjugacy problem is unsolvable.

Conventions: the group is fixed and the pair of words is the input. The word problem is the special case of the conjugacy problem in which $w_2$ is the empty word, so every finitely presented group with unsolvable word problem also has unsolvable conjugacy problem; the point of this theorem is that it came first and has a much simpler proof. Conversely, solvability of the word problem does not imply solvability of the conjugacy problem.

## Depends on

- [Solvable conjugacy problem for a quotient of a free group](../decision-problems-in-free-abelianized-extensions/conjugacy-problem-solvable.md)
- [Group](../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](novikov-unsolvable.md)

## Expansion

The statement follows from the unsolvability of the word problem: the word problem of a finitely presented group is the subproblem of its conjugacy problem in which the second word is empty, since a word is conjugate to the identity exactly when it represents the identity, so a group with unsolvable word problem has unsolvable conjugacy problem. Novikov's original proof came first and encodes an undecidable problem directly into conjugacy in an explicit finite presentation; the survey read below records that it is much simpler than his later proof for the word problem.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in the copy arXiv:1204.0299v2, where the definition and the statement, with its priority over the word problem, are in Section 6.3 ("The conjugacy problem").
- P. S. Novikov, *Unsolvability of the conjugacy problem in the theory of groups* (in Russian), Izv. Akad. Nauk SSSR Ser. Mat. 18 (1954), 485–524, the original source, cited beside the survey read above.
