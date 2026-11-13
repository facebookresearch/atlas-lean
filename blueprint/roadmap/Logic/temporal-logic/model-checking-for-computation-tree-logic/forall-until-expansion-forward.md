# One-step unfolding of universal until, forward direction

Let $\varphi$ and $\psi$ be CTL
formulas, and write $s \models \chi$ when the state $s$ of a labelled transition system satisfies
the formula $\chi$ under a given valuation of the atoms. If
$s \models \mathsf{A}[\varphi \mathbin{\mathsf{U}} \psi]$, then either $s \models \psi$, or
$s \models \varphi$, $s$ has at least one outgoing transition, and every state $t$ reached from $s$
by a single transition with any label satisfies
$t \models \mathsf{A}[\varphi \mathbin{\mathsf{U}} \psi]$.
