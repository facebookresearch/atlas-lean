# Iterated forward differences of a power as an alternating binomial sum

For a real
number $r$, let $\Delta_r$ be the forward difference operator with step $r$, sending a function
$f : \mathbb{R} \to \mathbb{R}$ to $y \mapsto f(y + r) - f(y)$, and let $\Delta_r^k$ be its
$k$-fold iterate (the identity when $k = 0$). For all real numbers $r$ and $x$ and all natural
numbers $k$ and $n$, applying $\Delta_r^k$ to the function $y \mapsto y^n$ and evaluating at $x$
gives $\sum_{j=0}^{k} (-1)^{k-j} \binom{k}{j} (x + rj)^n$.

The paper states this for nonzero complex $r$ and positive $k$; here $r$ is real and $k = 0$ is
allowed.

## Sources

- Fatima Zohra Bensaci, Rachid Boumahdi, and Laala Khaldi, "Finite Sums Involving Fibonacci and Lucas Numbers", Lemma 21.
