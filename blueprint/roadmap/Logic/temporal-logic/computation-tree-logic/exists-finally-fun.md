# The $\mathsf{EF}$ functional

Given a labelled transition system, a valuation of the atoms
at its states, and a CTL formula $\varphi$, this is the map sending a set of states $Z$ to the set
of states that satisfy $\varphi$ or have some successor in $Z$.

Its least fixed point is the set of states satisfying $\mathsf{EF}\,\varphi$.
