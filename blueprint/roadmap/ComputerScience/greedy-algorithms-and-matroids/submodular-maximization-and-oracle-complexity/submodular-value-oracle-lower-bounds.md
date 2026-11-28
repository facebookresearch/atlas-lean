# Value-oracle lower bounds for submodular maximization

Consider algorithms, deterministic or randomized and with unlimited computational power, that receive a budget $k$ as part of the input, access a normalized ($f(\emptyset) = 0$) monotone submodular function $f$ on a ground set of $n$ elements only through value queries, and return a set $S$ with $|S| \le k$. Fix an integer $q \ge 2$ and a ratio $\beta > 1 - (1 - 1/q)^q$. No such algorithm achieves the approximation ratio $\beta$, that is $f(S) \ge \beta \max_{|T| \le k} f(T)$, on every instance whose ground set size $n$ is a multiple of $q$ and whose budget is $k = n/q$ while making only $e^{o(n)}$ value queries. Since $1 - (1 - 1/q)^q$ decreases to $1 - 1/e$, this covers every fixed $\beta > 1 - 1/e$: beating the $(1 - 1/e)$-approximation of greedy under a cardinality constraint requires exponentially many value queries.

## Proof sketch

Symmetry-gap argument. On $X = \{1, \ldots, q\}$ take $f(S) = \min(|S|, 1)$ with budget $1$: the optimum is $1$, while the best symmetric fractional solution has multilinear value $1 - (1 - 1/q)^q$. Replacing each element of $X$ by a cluster of $\ell = n/q$ copies refines the budget-$1$ constraint to $|S| \le \ell = k$. Perturbing the multilinear extension near the symmetric region gives two monotone submodular functions on these $n$ elements whose values agree, with probability $1 - e^{-\Omega(\ell)}$ over a random relabelling, on every query in a fixed sequence of $e^{o(\ell)}$ queries, and only one of which has a feasible solution of value near $1$. As $q$ is fixed, $e^{o(\ell)} = e^{o(n)}$, so no algorithm with $e^{o(n)}$ queries beats ratio $1 - (1 - 1/q)^q$ under the budget $k = n/q$, for every fixed $q$, and $1 - (1 - 1/q)^q$ decreases to $1 - 1/e$. The budget has to grow with $n$: for a fixed budget $k$, querying all $O(n^k) = e^{o(n)}$ sets of size at most $k$ finds an optimal solution.

At the other extreme, for $k = 1$ a deterministic algorithm with ratio $c > 1/2$ on every normalized monotone submodular function on $n \ge 2$ elements makes at least $n - 1$ value queries on some function. Answer every query with $f_0(S) = \min(|S|, 2)$. If at most $n - 2$ queries are made, two singletons are unqueried and one of them, $\{y\}$, is not the returned set. The function $g(S) = \min(2, |S| + [y \in S])$ is a concave function of a nonnegative modular function, hence normalized, monotone and submodular, and agrees with $f_0$ except at $\{y\}$. The algorithm therefore behaves identically on $g$ and returns a set of $g$-value at most $1$, while $g(\{y\}) = 2$, so its ratio on $g$ is at most $1/2$.

## Depends on

- [Value and independence oracle models](value-and-independence-oracle-models.md)
- [Nemhauser-Wolsey-Fisher: greedy is a (1 - 1/e)-approximation under a cardinality constraint](nemhauser-wolsey-fisher-greedy.md)

## Sources

- G. L. Nemhauser and L. A. Wolsey, "Best Algorithms for Approximating the Maximum of a Submodular Set Function", Mathematics of Operations Research 3(3), 1978.
- J. Vondrák, "Symmetry and Approximability of Submodular Maximization Problems", SIAM Journal on Computing 42(1), 2013, Section 1 and Theorem 1.8.
- A. Krause and D. Golovin, "Submodular Function Maximization", in "Tractability: Practical Approaches to Hard Problems", Cambridge University Press, 2014, Section 2.
