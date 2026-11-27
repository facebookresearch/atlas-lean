# Classical form of $\mathsf{A}(\varphi\,\mathsf{U}\,\psi)$ on serial systems

Let $s$ be a
state of a serial labelled transition system with an atom valuation, and let $\varphi$ and $\psi$
be CTL formulas. Then $s$ satisfies $\mathsf{A}[\varphi\,\mathsf{U}\,\psi]$ if and only if $s$
satisfies neither $\mathsf{E}[\neg\psi\,\mathsf{U}\,(\neg\varphi \land \neg\psi)]$ nor
$\mathsf{EG}\,\neg\psi$. That is, no finite run from $s$ ends at a state satisfying
$\neg\varphi \land \neg\psi$ with $\neg\psi$ at all earlier states, and no infinite run from $s$
has $\neg\psi$ at every state.

The forward direction extends an $\mathsf{EU}$ witness to an infinite run; the backward
direction takes, on each infinite run, the least $\psi$-position and derives an $\mathsf{EU}$
witness from any earlier $\neg\varphi$-position.
