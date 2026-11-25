# Pole placement for single-input systems

Let $V$ be an $n$-dimensional vector space over a field, $A : V \to V$ linear and $b \in V$ such that $b, A b, \dots, A^{n-1} b$ span $V$ (the Kalman rank condition for the single-input system $\dot x = A x + b u$). Then for every monic polynomial $P$ of degree $n$ there is a linear form $K$ on $V$ such that the closed-loop operator $A + bK : x \mapsto A x + K(x) \, b$ has characteristic polynomial $P$.

This is the single-input case ($m = 1$) of the pole-shifting theorem (Wonham 1967; Coron, *Control and Nonlinearity*, AMS 2007, Theorem 10.1 over $\mathbb{R}$; Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Theorem 13, over any field). By Coron's Remark 10.5 the feedback is unique when $m = 1$; uniqueness is not part of the statement. The proof differs from Coron's, which passes through the controller form (Lemma 10.2): with $q$ the coordinate form dual to $A^{n-1} b$ in the basis $b, \dots, A^{n-1} b$ and $K = -q \circ P(A)$ (Ackermann's formula), one checks $q \circ (A + bK)^j = q \circ A^j$ for $j < n$ and $q \circ P(A + bK) = 0$; the forms $q \circ A^j$, $j < n$, separate points, so $P(A + bK) = 0$; and $b$ is still a cyclic vector of $A + bK$, so no nonzero polynomial of degree $< n$ annihilates $A + bK$ and $P$ is its characteristic polynomial (Cayley–Hamilton).

## Background

- [Kalman rank condition](../controllability-of-linear-systems/is-controllable-on-iff-kalman.md): the hypothesis is the single-input Kalman rank condition, equivalent to controllability; Coron's own proof (Lemma 10.2) uses this equivalence, the Ackermann proof given here does not.
