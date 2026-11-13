# CTL formulas

The formulas of computation tree logic over a type $A$ of atoms are
generated as follows: every atom $a \in A$ is a formula, $\top$ is a formula, and if $\varphi$
and $\psi$ are formulas then so are the negation $\neg\varphi$, the conjunction
$\varphi \land \psi$, the existential next $\mathsf{EX}\,\varphi$, the existential until
$\mathsf{E}[\varphi\,\mathsf{U}\,\psi]$, the existential globally $\mathsf{EG}\,\varphi$ and the
universal until $\mathsf{A}[\varphi\,\mathsf{U}\,\psi]$.

The universal until is primitive rather than the classical translation through $\mathsf{EU}$
and $\mathsf{EG}$, which is unsound on transition systems with deadlocked states.
