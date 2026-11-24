# Correctness of the finite fixed-point computation of EU

Let a labelled transition system
have finitely many states and finitely many labels, with decidable transitions and decidable
equality of states, and fix a valuation of the atoms. For a finite set $Z$ of states let
$\mathrm{Pre}_\exists(Z)$ be the set of states with a transition into $Z$, and for finite sets
$A$ and $B$ of states let $\mathrm{EU}_{\mathrm{fin}}(A, B)$ be the least fixed point of
$Z \mapsto B \cup (A \cap \mathrm{Pre}_\exists(Z))$, computed by finite iteration. Let $\varphi$
and $\psi$ be CTL formulas and $A$ and $B$ finite sets of states such that a state lies in $A$
exactly when it satisfies $\varphi$, and lies in $B$ exactly when it satisfies $\psi$. Then every
state $s$ lies in $\mathrm{EU}_{\mathrm{fin}}(A, B)$ if and only if $s$ satisfies
$\mathsf{E}[\varphi \mathbin{\mathsf{U}} \psi]$.
