# Offline k-server on pattern-avoiding requests in the unit interval

Let $\pi$ be a fixed permutation with Füredi–Hajnal limit $c_\pi$. Serve requests in $[0, 1]$ in order with $k \ge 1$ servers on the line, all starting at $0$, at cost the total server movement, and let $\mathrm{OPT}_k(X)$ be the optimal offline cost. For every sequence of pairwise distinct requests $X = (r_1, \dots, r_n) \in [0, 1]^n$ that avoids $\pi$ (as a sequence of reals), $\mathrm{OPT}_k(X) = O\big(k^{1 + \log_{5c_\pi} 120} \cdot n^{1/(\lfloor \log_{5c_\pi} k \rfloor + 1)}\big)$. Repeated requests are allowed at the price of replacing $c_\pi$ by the Füredi–Hajnal limit of the permutation obtained from $\pi$ by replacing each entry with a copy of $21$; so for $k \ge 2$ every $\pi$-avoiding $X \in [0,1]^n$, repeats included, has $\mathrm{OPT}_k(X) = k^{O(1)} n^{O_\pi(1/\log k)}$, and such a solution can be computed efficiently without knowing $\pi$. In contrast, for arbitrary request sequences in $[0,1]$ the optimal offline cost is at most $n/k + k$ (each server first moves, at cost at most $1$, into its own interval of length $1/k$ and then serves the requests there) and for every $n$ some input has optimal cost at least $n/(4k)$.

## Proof sketch

The proof uses a *distance-balanced* merge sequence, a variant of the Guillemot–Marx twin-width decomposition of pattern-avoiding point sets whose width is bounded in terms of $c_\pi$. Following the decomposition, the request sequence is split into a bounded number of parts at each level, and the servers are allotted to the parts according to their sizes, so that the movement at each level of the recursion is controlled; the number of levels is about $\log_{5c_\pi} k$, which yields the exponent of $n$.

## Depends on

- [Classical pattern containment in a sequence](../../../../Combinatorics/permutations/permutation-patterns/cyclic-pattern-avoiding-stack-sorting/contains-pattern-seq.md)
- [The k-server problem](../../../online-algorithms/paging-and-k-server/the-k-server-problem.md)
- [Marcus–Tardos theorem on excluded permutation matrices](marcus-tardos-theorem.md)

## Sources

- Benjamin Aram Berendsohn, László Kozma, Michal Opler, "Optimization with Pattern-Avoiding Input", STOC (2024), arXiv:2310.04236.
