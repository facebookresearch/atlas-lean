# $\mathsf{A}(\varphi\,\mathsf{U}\,\psi)$ at a deadlocked state

Let $s$ be a state of a
labelled transition system with an atom valuation, and suppose that $s$ is deadlocked: there is
no transition from $s$ under any label. Then for all CTL formulas $\varphi$ and $\psi$, $s$
satisfies $\mathsf{A}[\varphi\,\mathsf{U}\,\psi]$ if and only if $s$ satisfies $\psi$.

The infinite-run condition is vacuous, since an infinite run needs a step at index $0$, and the
constant finite run of length $0$ forces $\psi$ at $s$ itself.
