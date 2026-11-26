# Spectral arbitrariness of Tyaglov's sign pattern

The proposition that for every $n \ge 2$ and every monic real polynomial $q$ of degree $n$ there is a real $n \times n$ matrix $A$ whose entries have the signs prescribed by Tyaglov's pattern $S_n$ (positive where $S_n$ has $+$, negative where it has $-$, zero where it has $0$) with characteristic polynomial $\det(X I - A) = q$. Here, for $n \ge 2$, [Tyaglov's sign pattern](tyaglov-pattern.md) $S_n$ is the $n \times n$ matrix of signs (indices $0, \dots, n-1$) with $+$ on the superdiagonal (positions $(i, i+1)$), $-$ on the subdiagonal (positions $(i+1, i)$), $+$ in position $(0, 0)$, $-$ in position $(n-1, n-1)$, and $0$ elsewhere; the two corners are distinct because $n \ge 2$. (For $n = 1$ the definition gives the single entry the sign $+$, a case the proposition does not involve.) Equivalently, every real polynomial of degree $n$ with leading coefficient $(-1)^n$ is $\det(A - \lambda I)$ for such an $A$.

## Sources

- AimPL: Stability and hyperbolicity, Section 2 (Matrix Theory), Problem 2.4 (M. Tyaglov), American Institute of Mathematics problem lists, http://aimpl.org/hyperbolicpoly/2/.
