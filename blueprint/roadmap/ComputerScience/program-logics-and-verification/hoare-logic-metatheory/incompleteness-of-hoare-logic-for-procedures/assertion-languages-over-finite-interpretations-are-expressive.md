# Assertion languages over finite interpretations are expressive

If the assertion and expression languages $L_A$ and $L_E$ are first-order languages with equality and the domain of the interpretation $I$ is finite, then $L_A$ is expressive with respect to $L_E$ and $I$ for the [Algol-like programs with procedure parameters](algol-like-programs-with-procedure-parameters.md). Indeed, if $x_1, \dots, x_n$ are the variables free in $Q$ or global to $S$ or to a procedure of $e$, then membership of a state in $\mathrm{WP}(S, e, Q)$ depends only on the values of $x_1, \dots, x_n$, and the finitely many tuples of values in it can be listed as a finite disjunction of conjunctions of equations $x_i = a_i$.

## Depends on

- [Algol-like programs with procedure parameters](algol-like-programs-with-procedure-parameters.md)

## Sources

- E. M. Clarke, "Programming language constructs for which it is impossible to obtain good Hoare axiom systems", *Journal of the ACM* 26(1):129–147, 1979, <http://www.cs.cmu.edu/afs/cs.cmu.edu/user/emc/www/papers/Papers%20In%20Refereed%20Journals/79_impossible_hoareaxiom.pdf>, Section 2, Lemma 2.1.
