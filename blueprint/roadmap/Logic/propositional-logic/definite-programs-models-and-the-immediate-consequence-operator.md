# Definite programs, models and the immediate-consequence operator

For finite ground normal logic programs, finite sets of rules $a \leftarrow b_1, \dots, b_m, \mathrm{not}\ c_1, \dots, \mathrm{not}\ c_n$
over a finite set of atoms, this node collects the notions of definite program, model and immediate-consequence
operator; the reduct and stable models are defined separately.

## Expansion

A sound expansion has separate pages for:

1. **Definite programs:** a program is definite when every rule has an empty negative body.
2. **Interpretations and models:** an interpretation is a finite set of atoms; it satisfies a rule read
   classically when it contains the head whenever it contains the positive body and is disjoint from the
   negative body; a model satisfies every rule.
3. **Immediate-consequence operator:** $T_P(X)$ is the set of heads of rules whose positive body is
   contained in $X$ and whose negative body is disjoint from $X$.

## Sources

- V. Lifschitz, *Twelve definitions of a stable model*, ICLP 2008, LNCS 5366, 37–51, Section 1, rule form (1) and the classical reading of rules (formula (8), Section 6). <https://www.cs.utexas.edu/~vl/papers/12defs.pdf>
- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, 2004/05: Definition 2.1 (normal programs), Definition 2.4 (interpretations and $T_P$ with negative bodies) and Proposition 2.5 (models are the pre-fixed points of $T_P$). <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>
