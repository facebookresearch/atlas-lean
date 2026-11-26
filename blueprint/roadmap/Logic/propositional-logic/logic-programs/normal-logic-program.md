# Normal logic program

Fix a set of atoms. A *normal rule* is an expression

$$a \leftarrow b_1, \dots, b_m, \mathrm{not}\ c_1, \dots, \mathrm{not}\ c_n \qquad (m, n \ge 0)$$

of atoms $a, b_1, \dots, b_m, c_1, \dots, c_n$. The atom $a$ is its *head*, $\{b_1, \dots, b_m\}$ its *positive body* and $\{c_1, \dots, c_n\}$ its *negative body*; $\mathrm{not}$ is negation as failure. A *finite ground normal logic program* is a finite set of normal rules over a finite set of atoms. A rule is *definite* if its negative body is empty, and a program is *definite* if all its rules are.

A program with variables stands for the set of its ground instances over its Herbrand universe; the pages of this folder treat finite ground programs only.

## Sources

- P. Hitzler, *Operator-based semantics for logic programs*, lecture notes, TU Dresden, winter semester 2004/05, <https://people.cs.ksu.edu/~hitzler/topics/teaching/ws04/plecture.pdf>, Definition 2.1 (normal logic programs and definite programs) and Section 2.2.
- V. Lifschitz, "Foundations of logic programming", in G. Brewka (ed.), *Principles of Knowledge Representation*, CSLI Publications, 1996, pp. 69–127, <https://www.cs.utexas.edu/~vl/papers/flp.ps>, Section 3.8: normal rules and programs, those without classical negation.
