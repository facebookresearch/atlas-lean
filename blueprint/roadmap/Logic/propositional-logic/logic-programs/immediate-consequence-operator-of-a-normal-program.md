# Immediate-consequence operator of a normal program

Let $P$ be a [finite ground normal logic program](normal-logic-program.md) over a set $A$ of atoms. Its *immediate-consequence operator* $T_P : 2^A \to 2^A$ maps an interpretation $I$ to the set of heads of the rules of $P$ whose body is [true in $I$](models-of-a-normal-logic-program.md):

$$T_P(I) = \{a \mid a \leftarrow b_1, \dots, b_m, \mathrm{not}\ c_1, \dots, \mathrm{not}\ c_n \in P,\ b_1, \dots, b_m \in I,\ c_1, \dots, c_n \notin I\}.$$

For a definite program $T_P$ is monotone. When negative bodies occur it need not be monotone: for $P = \{p \leftarrow \mathrm{not}\ q\}$, $T_P(\emptyset) = \{p\}$ but $T_P(\{q\}) = \emptyset$.

## Depends on

- [Normal logic program](normal-logic-program.md)
- [Models of a normal logic program](models-of-a-normal-logic-program.md)

## Sources

- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, winter semester 2004/05, <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>, Definition 2.4 (the operator $T_P$ for normal programs) and the proof of Proposition 2.7 (monotonicity for definite programs). The non-monotone example applies Definition 2.4.
