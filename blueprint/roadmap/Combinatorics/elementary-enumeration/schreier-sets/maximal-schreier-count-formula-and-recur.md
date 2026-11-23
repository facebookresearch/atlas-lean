# Closed form and recurrence for maximal $(p, q)$-Schreier sets

Let $p$ and $q$ be positive
integers, put $p' = p / \gcd(p, q)$ and $q' = q / \gcd(p, q)$, and for each $n$ let
$|M^{p/q}_n|$ be the number of maximal $(p, q)$-Schreier sets with maximum $n$, that is, of sets
$F \subseteq \{1, \dots, n\}$ with $n \in F$ and $q \min F = p |F|$. For each $n$, let $K_n$ be
the set of integers $k$ with $1 \le k \le \lfloor (n+1)/(p'+q') \rfloor$ and $q'k \ge 2$, and let
$\delta_n$ be $1$ if $q' = 1$ and $n = p'$, and $0$ otherwise. Then for every $n \ge 0$,

$$|M^{p/q}_n| = \sum_{k \in K_n} \binom{n - p'k - 1}{q'k - 2} + \delta_n,$$

and for every $n \ge p + q + 1$,

$$|M^{p/q}_n| = \sum_{i=1}^{q} (-1)^{i+1} \binom{q}{i} |M^{p/q}_{n-i}| + |M^{p/q}_{n-(p+q)}|.$$

The paper prints the first formula as a sum over all $1 \le k \le \lfloor (n+1)/(p'+q') \rfloor$,
without $\delta_n$, and only for $1 \le n \le p + q$. Read with binomial coefficients vanishing
at negative lower index, it fails at $p = q = n = 1$, where $|M^{1/1}_1| = 1$ but the sum is $0$;
the term $\delta_n$ counts the singleton $\{n\}$, as in equation (10) of the paper's proof of
Theorem 1.

## Sources

- Hùng Việt Chu and Zachary Louis Vasseur, *Linear Recurrences of Generalized Schreier Sets Revisited*, Journal of Integer Sequences 29 (2026), Article 26.2.2, Corollary 3 (`jis-2026-26.2.2-cor-3`).
