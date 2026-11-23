# $\mathsf{EF}$ is a least fixed point

Fix a labelled transition system, a valuation of the
atoms at its states, and a CTL formula $\varphi$. Write $[\![\varphi]\!]$ for the set of states
satisfying $\varphi$ and $\mathrm{Pre}_\exists(Z)$ for the set of states having some successor in a
set of states $Z$. Then the set of states satisfying $\mathsf{EF}\,\varphi$ is the least fixed point
of the monotone operator $Z \mapsto [\![\varphi]\!] \cup \mathrm{Pre}_\exists(Z)$ on sets of states.

The fixed point is contained in $\mathsf{EF}\,\varphi$ by Park induction, using the one-step
expansion of $\mathsf{EF}$; the converse is induction on a path to a $\varphi$-state, unfolding the
fixed point once per step.
