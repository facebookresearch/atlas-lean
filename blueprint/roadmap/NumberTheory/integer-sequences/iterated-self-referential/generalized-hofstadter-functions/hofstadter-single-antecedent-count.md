# Values with exactly one preimage under a Hofstadter function

Let $k \ge 1$, let
$\alpha > 0$ satisfy $\alpha^k + \alpha - 1 = 0$ and let $\beta > 0$ satisfy
$\beta^k - \beta^{k-1} - 1 = 0$. Write $f^j$ for the $j$-fold iterate of a function $f$ and let
$F_k$ be the generalized Hofstadter function. Let $\tau_k$ be the substitution on letters with
$\tau_k(k) = k\,1$ and $\tau_k(i) = i + 1$ for $1 \le i < k$, let $x_k$ be the infinite word fixed
by $\tau_k$ that is the limit of the words $\tau_k^m(k)$, write $x_k[0:n)$ for its prefix of
length $n$ and let $L_k(n) = |\tau_k(x_k[0:n))|$. Let $U_k(n)$ be the number of $j$ with
$0 \le j < n$ for which exactly one natural number $m$ satisfies $F_k(m) = j$. Then for every
$n \ge 1$, $U_k(n) = 2n - 1 - L_k(n - 1)$ and $U_k(n) = n - F_k^{k-1}(n - 1)$. Moreover
$U_k(n)/n \to 1 - \alpha^{k-1}$ as $n \to \infty$, and $1 - \alpha^{k-1} = 2 - \beta$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Proposition 18 (`jis-2026-26.3.3-prop-18`).
