# Solutions of $P u^2 + Q u y + R y^2 = 1$ give convergents of $-Q/(2P)$

Let $P, Q, R, u, y$
be integers with $P > 0$ and $y > 0$, and let $D = Q^2 - 4PR$. Assume that $D < 0$, that
$D \ne -3$, and that $P \ne 2$ if $D = -4$. If $P u^2 + Q u y + R y^2 = 1$, then, writing
$\omega = -Q/(2P)$ with regular continued fraction expansion $\omega = [a_0; a_1, a_2, \dots]$,
there is a natural number $n$ such that $u/y$ equals the $n$-th convergent of $\omega$ and either
$n = 0$ or the partial quotient $a_n$ exists (the expansion has not terminated before $a_n$).

A solution of $P u^2 + Q u y + R y^2 = 1$ automatically has $\gcd(u, y) = 1$, as the source's
lemma requires; the exclusion $D \ne -3$ and the condition that $D = -4$ implies $P \ne 2$ are
exactly the source theorem's.

Proof: Following Matthews' theorem and lemma, complete the square, establish the Legendre
approximation bound, and choose the least convergent index so that termination cannot have
occurred earlier.

## Sources

- Keith R. Matthews, "Lagrange's Algorithm Revisited: Solving at^2 + btu + cu^2 = n in the Case of Negative Discriminant," Journal of Integer Sequences 17 (2014), Article 14.11.1, Theorem, lines 167–169, equation, lines 109–111, Lemma, lines 120–122, https://cs.uwaterloo.ca/journals/JIS/VOL17/Matthews/matt10.tex
