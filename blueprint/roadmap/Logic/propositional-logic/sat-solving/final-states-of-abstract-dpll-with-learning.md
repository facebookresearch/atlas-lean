# Final states of abstract DPLL with learning

Consider a derivation $\emptyset \parallel F \Longrightarrow_{\mathcal{L}}^* S$ in [abstract DPLL with learning](abstract-dpll-with-learning.md), where $S$ is final with respect to Basic DPLL. Then:

1. $S$ is FailState if and only if $F$ is unsatisfiable.
2. If $S$ is $M \parallel F'$, then every literal of $F'$ is defined in $M$, no clause of $F'$ is false in $M$, and $M$ is a model of $F$.

The same holds for derivations by the Basic DPLL system alone. The theorem does not claim confluence: a satisfiable $F$ may reach several final states, each with a model.

**Proof.** Along any derivation from $\emptyset \parallel F$ the following invariants hold:
- the current clause set is equivalent to $F$, because learned and forgotten clauses are entailed;
- if $M = M_0\, l_1\, M_1 \cdots l_n\, M_n$ with decision literals $l_i$, then $F, l_1, \dots, l_i \models M_i$.

Whenever some clause is false in $M$, either Fail applies (no decision literal) or Backjump applies, with the negations of the decision literals as a backjump clause. So in a final state $M \parallel F'$ all literals are defined and no clause is false, which makes $M$ a model of $F'$ and hence of $F$. Conversely, FailState arises from some $M \parallel F'$ with no decision literal and a clause $C$ false in $M$. Then $F \models C$, and $F \models \neg C$ by the second invariant at level 0, so $F$ is unsatisfiable.

## Depends on

- [Abstract DPLL with learning](abstract-dpll-with-learning.md)

## Sources

- R. Nieuwenhuis, A. Oliveras and C. Tinelli, "Solving SAT and SAT modulo theories: from an abstract Davis–Putnam–Logemann–Loveland procedure to DPLL(T)", *Journal of the ACM* 53(6):937–977, 2006, <https://www.cs.upc.edu/~roberto/papers/JACM2006.pdf>, Section 2.5: Lemma 2.7 (invariants of derivations), Lemma 2.8 (Fail or Backjump applies to any state with a conflicting clause), Lemma 2.9 (final states), and Theorem 2.12 (FailState if and only if $F$ is unsatisfiable; otherwise $M$ is a model of $F$), with the remark on confluence.
