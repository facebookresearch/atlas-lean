# LTL satisfiability by the lasso criterion

An LTL formula is satisfiable iff its Büchi automaton has an accepting state that is reachable
from an initial state and lies on a nonempty cycle. With the lasso word of that cycle, a
satisfiable formula has an ultimately periodic model $u v^\omega$ (not stated separately here).

## Informally uses

- [Lasso characterization of Büchi nonemptiness](../../../TheoryOfComputation/omega-automata-and-games/emptiness-of-b-chi-automata/language-nonempty-iff-has-lasso.md):
  the automaton has finitely many states.
- [Büchi automaton accepts exactly the satisfying words](mem-buchi-iff.md).

## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 4.1, Theorem 24, with Proposition 13.
