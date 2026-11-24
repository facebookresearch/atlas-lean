# The existential-until functional

In a labelled transition system with a valuation of
atoms, let $\varphi$ and $\psi$ be CTL formulas. The existential-until functional sends a set $Z$
of states to the set of states $s$ such that either $s$ satisfies $\psi$, or $s$ satisfies
$\varphi$ and some transition leads from $s$ to a state in $Z$.

Its least fixed point is the set of states satisfying $\mathsf{E}[\varphi \,\mathsf{U}\, \psi]$.
