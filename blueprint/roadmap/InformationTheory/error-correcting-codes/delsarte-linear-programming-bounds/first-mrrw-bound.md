# First McEliece-Rodemich-Rumsey-Welch bound

Let $R(\delta) = \limsup_{n \to \infty} \frac1n \log_2 A(n, \lfloor \delta n \rfloor)$. For $0 < \delta < 1/2$,

$$
R(\delta) \le H_2\!\left(\tfrac12 - \sqrt{\delta(1 - \delta)}\right),
$$

where $H_2$ is the binary entropy function. It improves the Elias–Bassalygo bound for $\delta$ above about $0.15$; for smaller $\delta$ the Elias–Bassalygo bound is stronger.

## Proof sketch

Apply the dual LP bound to $f(x) = \frac{1}{a - x}\big(K_{t+1}(x)K_t(a) - K_t(x)K_{t+1}(a)\big)^2$ with $a$ slightly below the smallest root $x_1(t)$ and $t$ chosen so that $x_1(t) \approx d$. The Christoffel-Darboux formula shows $f$ has nonnegative Krawtchouk coefficients, and $f(i) \le 0$ for $i \ge d$ because $a < d$. Evaluating $f(0)/f_0$ asymptotically gives $\binom{n}{t}$ up to polynomial factors with $t/n \to \tau$ where $\frac12 - \sqrt{\tau(1-\tau)} = \delta$, i.e. $\tau = \frac12 - \sqrt{\delta(1-\delta)}$.

## Depends on

- [Elias–Bassalygo bound (alphabet-free form)](../bounds-on-code-size/elias-bassalygo-bound.md)

## Proof depends on

- [Delsarte's linear programming bound](delsarte-linear-programming-bound.md)
- [Christoffel-Darboux formula for Krawtchouk polynomials](christoffel-darboux-formula-for-krawtchouk-polynomials.md)
- [Asymptotics of the smallest root of Krawtchouk polynomials](asymptotics-of-the-smallest-krawtchouk-root.md)
- [Volume of a Hamming ball, entropy upper bound](../bounds-on-code-size/sum-choose-mul-pow-le-exp.md)

## Sources

- Robert J. McEliece, Eugene R. Rodemich, Howard Rumsey Jr., Lloyd R. Welch, "New upper bounds on the rate of a code via the Delsarte-MacWilliams inequalities", IEEE Transactions on Information Theory 23(2) (1977).
