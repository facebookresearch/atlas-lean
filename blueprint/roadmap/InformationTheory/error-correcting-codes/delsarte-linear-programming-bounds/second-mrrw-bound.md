# Second McEliece-Rodemich-Rumsey-Welch bound

For $0 < \delta < 1/2$,

$$
R(\delta) \le \min_{0 \le u \le 1 - 2\delta} \Big\{ 1 + g(u^2) - g(u^2 + 2\delta u + 2\delta) \Big\}, \qquad g(x) = H_2\!\left(\frac{1 - \sqrt{1 - x}}{2}\right),
$$

which coincides with the first bound for $\delta \ge 0.273$ and is strictly better for smaller $\delta$.

## Proof sketch

Combine the LP bound for constant-weight codes, obtained from the Johnson association scheme with Hahn polynomials in place of Krawtchouk polynomials, with an Elias-Bassalygo type averaging argument that relates $A(n, d)$ to the maximum size of constant-weight codes in Hamming spheres of radius $w$; optimizing $w = un$-type parameters yields the formula.

## Depends on

- [First McEliece-Rodemich-Rumsey-Welch bound](first-mrrw-bound.md)

## Proof depends on

- [Elias–Bassalygo bound (alphabet-free form)](../bounds-on-code-size/elias-bassalygo-bound.md)

## Sources

- Robert J. McEliece, Eugene R. Rodemich, Howard Rumsey Jr., Lloyd R. Welch, "New upper bounds on the rate of a code via the Delsarte-MacWilliams inequalities", IEEE Transactions on Information Theory 23(2) (1977).
