# Common lift count

Let $f \in \mathbb{Z}[x, y]$, let $p$ and $k$ be natural numbers and
let $P = ((r_1, s_1), \dots, (r_k, s_k))$ be a $k$-tuple of pairs of natural numbers. The common
lift count of $P$ is the number of pairs $(a, b)$ of natural numbers with $a, b < p$ such that
$p^2$ divides $f(r_i + ap, s_i + bp)$ for every $i$.

For a prime $p$ this says that every lift $(r_i + ap, s_i + bp)$ has $p$-adic valuation of $f$
greater than $1$ (a zero value counts as valuation greater than $1$); divided by $p^2$, the count
is the probability of this event for a uniformly random $(a, b) \in \mathbb{F}_p^2$.

## Sources

- Krishnan Rajkumar and Shubham, *On the Distribution of Points of Valuation 1 for a Polynomial in Two Variables*, INTEGERS 26 (2026), Article A82, Section 3 (definition of the indicator random variables `Y_{x,y}`).
