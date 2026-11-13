# Limits of Hofstadter iterates and letter frequencies

Let $k \ge 1$ and $j \ge 0$, let
$\alpha > 0$ satisfy $\alpha^k + \alpha - 1 = 0$ and let $\beta > 0$ satisfy
$\beta^k - \beta^{k-1} - 1 = 0$. Write $f^j$ for the $j$-fold iterate of a function $f$ and let
$F_k$ be the generalized Hofstadter function. Let $\tau_k$ be the substitution on letters with
$\tau_k(k) = k\,1$ and $\tau_k(i) = i + 1$ for $1 \le i < k$, let $x_k$ be the infinite word fixed
by $\tau_k$ that is the limit of the words $\tau_k^m(k)$, write $x_k[m]$ for its letter at index
$m$ (counting from $0$) and $x_k[0:n)$ for its prefix of length $n$, let
$L_k(n) = |\tau_k(x_k[0:n))|$, and for a letter $i$ let $C_k^{(=i)}(n)$ be the number of indices
$m < n$ with $x_k[m] = i$. Then, as $n \to \infty$: $F_k^j(n)/n \to \alpha^j$;
$L_k^j(n)/n \to \beta^j$; $C_k^{(=i)}(n)/n \to \alpha^{k+i-1}$ for every $i$ with $1 \le i < k$;
and $C_k^{(=k)}(n)/n \to \alpha^{k-1}$. Moreover $\alpha^{k-1} = \beta - 1$.

## Sources

- Pierre Letouzey, Shuo Li, and Wolfgang Steiner, *Pointwise Order of Generalized Hofstadter Functions G, H, and Beyond*, Journal of Integer Sequences 29 (2026), Article 26.3.3, Theorem 14 (`jis-2026-26.3.3-thm-14`).
