# Existential next via the predecessor operator

In a labelled transition system with a
valuation of atoms, let $\varphi$ be a CTL formula and write $\mathrm{Sat}(\varphi)$ for the set
of states satisfying $\varphi$. A state $s$ satisfies $\mathsf{EX}\,\varphi$ if and only if $s$
belongs to the existential predecessor set of $\mathrm{Sat}(\varphi)$, that is, some transition
leads from $s$ to a state satisfying $\varphi$.
