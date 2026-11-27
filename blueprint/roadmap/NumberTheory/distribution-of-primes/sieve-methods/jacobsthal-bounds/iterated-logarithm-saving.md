# An iterated-logarithm saving for Jacobsthal’s function

For a natural $k\ge1$, a length $m\in\mathbb N$ is admissible if for every positive natural
modulus $n$ with at most $k$ distinct prime divisors and every $a\in\mathbb Z$ there is a natural
$i<m$ with $\gcd(|a+i|,n)=1$. Thus the interval runs from $a$ to $a+m-1$, with signed starts allowed.

There is an absolute $C>0$ such that for every $k\ge1$ one can choose such an admissible $m$ with
$m\le Ck^2/(\log\log(3k))^2$.

## Expansion

State and establish the technical sieve estimates with their uniformity over prime sets and arbitrary interval starts. Separate explicit large-$k$ estimates furnishing the double-logarithmic saving from the finite range and check the positive denominator $\log\log(3k)$ for all $k\ge1$.

## Sources

- [JacobsthalImproved.lean — `erdos_970_iterated_log`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/JacobsthalImproved.lean#L22-L24)
