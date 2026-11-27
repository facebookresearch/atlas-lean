# Automatability implies feasible interpolation for systems closed under restriction

Let $P$ be a proof system closed under restrictions: if $\pi$ is a $P$-refutation of $F$ and $\rho$ is a partial assignment, then $\pi$ restricted by $\rho$ yields a $P$-refutation of the restricted formula $F|_\rho$ of no larger size. Say that $P$ is automatable in time $t$ if some algorithm, given an unsatisfiable formula $F$, outputs a $P$-refutation of $F$ within time $t(|F| + s_P(F))$, where $s_P(F)$ is the minimum size of a $P$-refutation of $F$. If $P$ is automatable in time $t$, then $P$ has **feasible interpolation** in time $\operatorname{poly}(t)$: given a $P$-refutation of size $s$ of a split formula $A(x, y) \wedge B(x, z)$, whose two parts share only the variables $x$, and an assignment $a$ to $x$, one can choose in time $t(|A| + s) + \operatorname{poly}(|A| + |B| + s)$ a side $C \in \{A, B\}$ such that $C(a, \cdot)$ is unsatisfiable.

## Proof sketch

Run the automating algorithm on $A(a, y)$ for $t(|A| + s)$ steps and check its output with the polynomial-time verifier of $P$. If it returns a valid refutation of $A(a, y)$, answer $A$; this is correct. Otherwise (a timeout or an invalid output) answer $B$. To see that $B(a, \cdot)$ is then unsatisfiable, suppose it had a satisfying assignment $b$. Restricting the given refutation by $x = a$ and $z = b$ satisfies every clause of $B$ and leaves a $P$-refutation of $A(a, y)$ of size at most $s$, so $s_P(A(a, y)) \le s$ and the automating algorithm would have produced a valid refutation within the time bound. The argument uses only closure under restrictions and automatability; it needs no interpolation theorem and no proof-length lower bound.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Sources

- M. L. Bonet, T. Pitassi, R. Raz, "On interpolation and automatization for Frege systems", SIAM Journal on Computing 29 (2000) 1939-1967, doi:10.1137/S0097539798353230.
- R. Impagliazzo, comment recorded in M. L. Bonet, T. Pitassi, R. Raz (2000); see also J. Krajíček, "Proof complexity", Cambridge University Press (2019).
- J. Krajíček, "Proof complexity", Encyclopedia of Mathematics and its Applications 170, Cambridge University Press (2019).
