# The infinitely-often automaton recognizes G F φ

Let $\varphi$ be a propositional
formula and $p$ the set of letters (sets of atoms) at which $\varphi$ evaluates to true. The
two-state Büchi automaton for “infinitely often $p$” accepts exactly the infinite words that
satisfy the LTL formula $\mathbf{G}\,\mathbf{F}\,\varphi$, where an atom $a$ holds at a letter $s$
iff $a \in s$. Equivalently, a word is accepted iff $\varphi$ holds at infinitely many positions.
