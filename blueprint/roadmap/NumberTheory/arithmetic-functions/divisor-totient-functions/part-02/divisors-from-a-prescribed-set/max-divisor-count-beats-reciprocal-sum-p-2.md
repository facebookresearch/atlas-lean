# Divisor counts from a set outgrow every power of its reciprocal sum

For every infinite set $A$ of natural numbers, every natural number $k$ and every real $M$, there are infinitely many natural numbers $x$ with

$$\max_{1 \le n < x} d_A(n) > M \Bigl(\sum_{n \in A,\ 1 \le n < x} \frac1n\Bigr)^k,$$

where $d_A(n)$ is the number of elements of $A$ dividing $n$ (the maximum is $0$ when $x \le 1$). That is, the quotient has limit superior $\infty$.

This resolves [Erdős Problem 444 (divisors from a set versus its reciprocal sum)](max-divisor-count-beats-reciprocal-sum-p.md), the statement recorded as a proposition, in the affirmative; the resolution is due to Erdős and Sárközy (1980), cited under Sources.

## Sources

- T. F. Bloom, Erdős Problems, Problem #444, https://www.erdosproblems.com/444.
- P. Erdős and A. Sárközy, Some asymptotic formulas on generalized divisor functions. IV, Studia Sci. Math. Hungar. (1980), 467–479.
