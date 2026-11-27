# Announcement elimination

Consider the language built from atoms, falsity, implication, the knowledge operators $K_i$ and announcements $[\varphi!]\psi$, without common knowledge. Its translation $t$ is defined by recursion on formulas under an ambient announcement condition $c$, starting from $c = \top$: an atom $a$ becomes $c \to a$, falsity becomes $c \to \bot$, implications are translated componentwise, $K_i\psi$ becomes $c \to K_i t_c(\psi)$, and $[\chi!]\psi$ becomes $t_{c \wedge t_c(\chi)}(\psi)$. Then every formula $\psi$ of the language is equivalent to its translation: they hold at the same worlds of every [epistemic model](../model.md).

## Sources

- H. van Ditmarsch, W. van der Hoek and B. Kooi, *Dynamic Epistemic Logic*, Springer, 2007, Chapter 4 (public announcement logic and its reduction axioms)
- A. Baltag and B. Renne, "Dynamic epistemic logic", *Stanford Encyclopedia of Philosophy*, the axiomatic theory PAL with its reduction axioms and the PAL Reduction Theorem, <https://plato.stanford.edu/entries/dynamic-epistemic/>
