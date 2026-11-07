# Büchi automata for the restricted safety fragment

Take as letters the sets of atoms,
an atom $a$ holding at a letter $s$ iff $a \in s$. For every formula $\psi$ of the restricted
safety fragment there is a nondeterministic Büchi automaton with finitely many states whose
ω-language is exactly the set of infinite words satisfying $\psi$, read as an LTL formula.

The finite state set is what makes the automaton a certificate of ω-regularity: every
ω-language is accepted by some Büchi automaton with infinitely many states. The fragment applies
the always operator $\mathbf{G}$ only to propositional formulas, so for example
$\mathbf{G}(p \vee \mathbf{X}\,q)$, for atoms $p$ and $q$ and the next operator $\mathbf{X}$, is
not covered.
