# Automatability implies feasible interpolation for systems closed under restriction

Let $P$ be a proof system closed under restrictions (a refutation of $F$ restricted by a partial assignment is a refutation of the restricted formula of no larger size). If $P$ is automatable in time $t$, then $P$ has **feasible interpolation** in time $\operatorname{poly}(t)$: given a $P$-refutation of size $s$ of a split formula $A(x, y) \wedge B(x, z)$ and an assignment $a$ to the shared variables $x$, one can decide in time $\operatorname{poly}(t(s))$ a side $C \in \{A, B\}$ such that $C(a, \cdot)$ is unsatisfiable.

## Proof sketch

Run the automating algorithm on $A(a, y)$ for $t(c \cdot s)$ steps, where the restriction of the given refutation to $x = a$ splits into refutations of $A(a,y)$ or of $B(a,z)$ of size at most $s$. If the algorithm finds a refutation of $A(a, y)$ within the time bound, answer $A$; otherwise $A(a, y)$ has no refutation of size $s$, so the restriction must refute $B(a, z)$, and answer $B$.

## Depends on

- [Automatable proof systems](automatable-proof-system.md)

## Proof depends on

- [Craig interpolation for first-order logic](../craig-interpolation-for-first-order-logic.md)

## Sources

- M. L. Bonet, T. Pitassi, R. Raz, "On interpolation and automatization for Frege systems", SIAM Journal on Computing 29 (2000) 1939-1967.
- R. Impagliazzo, comment recorded in M. L. Bonet, T. Pitassi, R. Raz (2000); see also J. Krajíček, "Proof complexity", Cambridge University Press (2019).
- J. Krajíček, "Proof complexity", Encyclopedia of Mathematics and its Applications 170, Cambridge University Press (2019).
