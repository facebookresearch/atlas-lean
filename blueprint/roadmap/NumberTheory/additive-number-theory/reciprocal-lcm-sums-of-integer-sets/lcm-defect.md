# Gcd defect

For a set $A$ of natural numbers and a real number $x$, let
$S_A(x) = \sum_{n \in A,\ 1 \le n \le x} 1/n$ be the harmonic sum of $A$ up to $x$, and let
$G_A(x)$ be the sum of $\gcd(n, m)/(nm)$ over all ordered pairs $(n, m)$ with $n, m \in A$,
$1 \le n \le x$ and $1 \le m \le x$. The gcd defect of $A$ up to $x$ is
$\mathcal{E}_A(x) = G_A(x)/S_A(x)^2 - 1$, where division by $0$ gives $0$; in particular
$\mathcal{E}_A(x) = -1$ when $A$ has no element in $[1, x]$.

When $A$ has an element in $[1, x]$, $\mathcal{E}_A(x) + 1$ is the expected value of
$\gcd(n, m)$ for $n$ and $m$ drawn independently from $A \cap [1, x]$, each with probability
proportional to $1/n$, so $\mathcal{E}_A(x)$ is the quantity $\mathbb{E} \gcd(n, m) - 1$ of the
source.

## Sources

- Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*, INTEGERS 24 (2024), Article A100, Equation (9).
