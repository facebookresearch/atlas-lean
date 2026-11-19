# Correctness of the finite fixed-point computation of EG

Let a labelled transition system
have finitely many states and finitely many labels, with decidable transitions and decidable
equality of states, and fix a valuation of the atoms. For a finite set $Z$ of states let
$\mathrm{Pre}_\exists(Z)$ be the set of states with a transition into $Z$, and for a finite set
$A$ of states let $\mathrm{EG}_{\mathrm{fin}}(A)$ be the greatest fixed point of
$Z \mapsto A \cap \mathrm{Pre}_\exists(Z)$, computed by finite iteration. Let $\varphi$ be a CTL
formula and $A$ a finite set of states such that a state lies in $A$ exactly when it satisfies
$\varphi$. Then every state $s$ lies in $\mathrm{EG}_{\mathrm{fin}}(A)$ if and only if $s$
satisfies $\mathsf{EG}\,\varphi$.
