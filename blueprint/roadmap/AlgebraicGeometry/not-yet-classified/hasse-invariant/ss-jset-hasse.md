# Supersingular $j$-invariants through the Hasse invariant

Let $K$ be a finite field of
characteristic $p \ne 2$, so that $p$ is an odd prime. A value $j \in K$ lies in
`ssJSetHasse p K` when every elliptic curve $W$ over $K$ with $j$-invariant $j$ has vanishing
Hasse invariant `W.hasseInvariant p`.

Since $2$ is invertible in $K$, $(x, y) \mapsto (x, 2y + a_1x + a_3)$ identifies $W$ with the
curve $Y^2 = \Psi(x)$, where $\Psi$ is `W.twoTorsionPolynomial`, and `W.hasseInvariant p` is the
coefficient of $x^{p-1}$ in $\Psi(x)^{(p-1)/2}$.

Reference: by the Hasse criterion (Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed.,
Theorem V.4.1(a)), an elliptic curve $Y^2 = f(x)$ over a finite field of characteristic $p \ge 3$
is supersingular if and only if the coefficient of $x^{p-1}$ in $f(x)^{(p-1)/2}$ is zero. So $j$
lies in this set exactly when the elliptic curves over $K$ with $j$-invariant $j$ are
supersingular.
