# Logarithmic gcd moment

For a set $A$ of natural numbers and a real number $x$, the
logarithmic gcd moment of $A$ up to $x$ is the sum of $\gcd(n, m)/(nm)$ over all ordered pairs
$(n, m)$ with $n, m \in A$, $1 \le n \le x$ and $1 \le m \le x$.

When $A \cap [1, x]$ is nonempty, dividing by $\big(\sum_{n \in A,\ 1 \le n \le x} 1/n\big)^2$
gives the expected value of $\gcd(n, m)$ for $n$ and $m$ drawn independently from $A \cap [1, x]$,
each with probability proportional to $1/n$.

## Sources

- Terence Tao, *Dense Sets of Natural Numbers with Unusually Large Least Common Multiples*, INTEGERS 24 (2024), Article A100, Equation (9).
