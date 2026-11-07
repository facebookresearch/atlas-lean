# The new-information zones as tower levels

Let $\ell \ge 2$ and let $r$ satisfy
$F_\ell \le r < F_{\ell+1}$, where $F_1 = F_2 = 1, F_3 = 2, \dots$ are the Fibonacci numbers. For
a Zeckendorf-adic integer $x = (x_i)_{i \ge 2}$ let $v_k(x) = \sum_{i=2}^{k+1} x_i F_i$, and let
$\mathrm{NIZ}_k$ be the new-information zone of order $k$ for $r$. Then for every
Zeckendorf-adic integer $x$: $x \notin \mathrm{NIZ}_k$ whenever $2 \le k \le \ell - 1$;
$x \in \mathrm{NIZ}_\ell$ if and only if $v_\ell(x) + r < F_{\ell+1}$;
$x \in \mathrm{NIZ}_{\ell+1}$ if and only if $F_{\ell+1} \le v_{\ell+1}(x) + r < F_{\ell+2}$; and
for every $k > \ell + 1$, $x \in \mathrm{NIZ}_k$ if and only if $F_k \le v_k(x) + r$ and
$v_k(x) < F_k$.

Since level $j$ of the large tower of order $k$ is $\{v_k = j - 1\}$, this says that
$\mathrm{NIZ}_\ell$ consists of the first $F_{\ell+1} - r$ levels of the large tower of order
$\ell$, $\mathrm{NIZ}_{\ell+1}$ of the levels $F_{\ell+1} - r + 1, \dots, F_{\ell+2} - r$ of the
large tower of order $\ell + 1$, and $\mathrm{NIZ}_k$ for $k > \ell + 1$ of the levels
$F_k - r + 1, \dots, F_k$ of the large tower of order $k$ (as subsets of the Zeckendorf-adic
integers).

## Sources

- Yohan Hosten, *On the Variation of the Sum of Digits in the Zeckendorf Representation: An Algorithm to Compute the Distribution and Mixing Properties*, Journal of Integer Sequences 27 (2024), Article 24.3.2, Proposition 29 (`jis-2024-24.3.2-prop-29`).
