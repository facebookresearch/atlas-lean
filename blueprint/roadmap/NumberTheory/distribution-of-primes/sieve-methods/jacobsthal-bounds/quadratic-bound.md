# A quadratic bound for Jacobsthal’s function

For a natural $k\ge1$, a length $m\in\mathbb N$ is admissible if for every positive natural
modulus $n$ with at most $k$ distinct prime divisors and every $a\in\mathbb Z$ there is a natural
$i<m$ with $\gcd(|a+i|,n)=1$. Thus the interval runs from $a$ to $a+m-1$, with signed starts allowed.

There is an absolute real $C>0$ such that every natural $k\ge1$ admits such an $m$ with $m\le Ck^2$.

## Proof depends on

- [Bound with an iterated-logarithm saving](iterated-logarithm-saving.md)

## Proof outline

Either establish the quadratic interval sieve bound directly, or derive this weaker statement from the sharper bound using a uniform positive lower bound on $\log\log(3k)$ for $k\ge1$. No assertion about the optimal order of growth is involved.

## Sources

- [Jacobsthal.lean — `erdos_970_quadratic`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Jacobsthal.lean#L24-L26)
