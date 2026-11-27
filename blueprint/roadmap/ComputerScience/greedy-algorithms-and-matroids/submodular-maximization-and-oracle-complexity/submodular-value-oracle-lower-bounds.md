# Value-oracle lower bounds for submodular maximization

Consider algorithms, deterministic or randomized and with unlimited computational power, that access a normalized ($f(\emptyset) = 0$) monotone submodular function $f$ on a ground set of $n$ elements only through value queries and return a set $S$ with $|S| \le k$. For every fixed $\beta > 1 - 1/e$, no such algorithm achieves the approximation ratio $\beta$, that is $f(S) \ge \beta \max_{|T| \le k} f(T)$, on every instance while making only $e^{o(n)}$ value queries: beating the $(1 - 1/e)$-approximation of greedy under a cardinality constraint requires exponentially many value queries.

## Proof sketch

Symmetry-gap argument. On $X = \{1, \ldots, k\}$ take $f(S) = \min(|S|, 1)$ with budget $1$: the optimum is $1$, while the best symmetric fractional solution has multilinear value $1 - (1 - 1/k)^k$. Replacing each element of $X$ by a cluster of $n$ copies and perturbing the multilinear extension near the symmetric region gives two monotone submodular functions whose values agree, with probability $1 - e^{-\Omega(n)}$ over a random relabelling, on every query in a fixed sequence of $e^{o(n)}$ queries, and only one of which has a solution of value near $1$. So no algorithm with $e^{o(n)}$ queries beats ratio $1 - (1 - 1/k)^k$, for every fixed $k$, and $1 - (1 - 1/k)^k$ decreases to $1 - 1/e$.

At the other extreme, for $k = 1$ a deterministic algorithm with ratio $c > 1/2$ on every normalized monotone submodular function on $n \ge 2$ elements makes at least $n - 1$ value queries on some function. Answer every query with $f_0(S) = \min(|S|, 2)$. If at most $n - 2$ queries are made, two singletons are unqueried and one of them, $\{y\}$, is not the returned set. The function $g(S) = \min(2, |S| + [y \in S])$ is a concave function of a nonnegative modular function, hence normalized, monotone and submodular, and agrees with $f_0$ except at $\{y\}$. The algorithm therefore behaves identically on $g$ and returns a set of $g$-value at most $1$, while $g(\{y\}) = 2$, so its ratio on $g$ is at most $1/2$.

## Depends on

- [Value and independence oracle models](value-and-independence-oracle-models.md)

## Sources

- G. L. Nemhauser and L. A. Wolsey, "Best Algorithms for Approximating the Maximum of a Submodular Set Function", Mathematics of Operations Research 3(3), 1978.
- J. Vondrák, "Symmetry and Approximability of Submodular Maximization Problems", SIAM Journal on Computing 42(1), 2013, Section 1 and Theorem 1.8.
- A. Krause and D. Golovin, "Submodular Function Maximization", in "Tractability: Practical Approaches to Hard Problems", Cambridge University Press, 2014, Section 1.
