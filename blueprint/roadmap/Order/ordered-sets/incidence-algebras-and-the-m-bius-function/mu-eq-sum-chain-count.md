# Philip Hall's theorem

Let $a, b$ be elements of a locally finite poset and let $c_i$ be the number of chains
$a = t_0 < t_1 < \cdots < t_i = b$ of length $i$. Then

$$\mu(a, b) = c_0 - c_1 + c_2 - c_3 + \cdots,$$

a finite sum since $c_i = 0$ once $i \ge |[a, b]|$.

Stanley states it for $\mu_{\hat P}(\hat 0, \hat 1)$, where $\hat P$ is a finite poset $P$ with a
least element $\hat 0$ and a greatest element $\hat 1$ adjoined. For $a < b$ the interval $[a, b]$
is $\hat P$ for $P$ the open interval $(a, b)$; for $a = b$ both sides equal $1$. Since $c_{i}$
counts the $(i-2)$-dimensional faces of the order complex of $P$ for $i \ge 1$, the theorem says
that $\mu_{\hat P}(\hat 0, \hat 1)$ is the reduced Euler characteristic of that complex (Stanley,
Proposition 3.8.6), which links the Möbius function to topology.

Stanley's proof expands $\mu = (1 + (\zeta - 1))^{-1}$ as a geometric series in the incidence
algebra. Induction on $|[a, b]|$ from the recurrences for $c_{i+1}$ and for $\mu$ also
proves it.

## Sources

- R. P. Stanley, *Enumerative Combinatorics*, vol. 1, 2nd ed., author's draft of 15 July 2011, https://math.mit.edu/~rstan/ec/ec1.pdf, Proposition 3.8.5.
