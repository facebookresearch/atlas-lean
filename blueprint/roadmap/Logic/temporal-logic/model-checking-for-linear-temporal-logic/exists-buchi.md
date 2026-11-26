# Every LTL formula has a finite-state Büchi automaton

For every LTL formula $\varphi$ and every valuation of its atoms on the input letters, some
finite-state nondeterministic Büchi automaton accepts exactly the infinite words that satisfy
$\varphi$. Neither the atoms nor the alphabet need be finite or decidable.

This is the existence part of the Vardi–Wolper translation; the automaton is the degeneralized
truth-annotation tableau. The same automaton has at most $4^{|\varphi|}$ states, which is the
form of the translation used for complexity bounds.


Applied to a formula of the general safety fragment of LTL (propositional formulas closed under conjunction, disjunction, next, and always applied to a safety formula), read as an LTL formula over sets of atoms, this gives a finite-state Büchi automaton for that formula. It does not give the stronger safety-automaton form of O. Kupferman and M. Y. Vardi (Formal Methods in System Design 19, 2001), in which every state is accepting.
## Sources

- M. Y. Vardi, "An automata-theoretic approach to linear temporal logic", in *Logics for Concurrency: Structure versus Automata*, LNCS 1043, Springer 1996, pp. 238-266. Numbering from the author's posted version (https://www.cs.rice.edu/~vardi/papers/banff94rj.pdf), which may differ from the published text. Section 3, Corollary 23.
- M. Y. Vardi and P. Wolper, "Reasoning about infinite computations", *Information and Computation* 115 (1994), 1-37.
