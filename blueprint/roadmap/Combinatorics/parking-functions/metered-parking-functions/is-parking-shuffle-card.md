# Number of parking-function shuffles

Let $1 \le m \le n$ and $1 \le k \le n$, and write
$\mathrm{Sh}_m(k - 1, n - k)$ for the set of $(m, n)$-parking-function shuffles with parameter
$k$, words of length $m - 1$ with entries in $\{0, \dots, n-1\}$. Then
$|\mathrm{Sh}_m(k - 1, n - k)|$ equals $\binom{m-1}{n-k}(n-m+1)\,k^{m-n+k-2}(n-k+1)^{n-k-1}$
if $k > n - m + 1$, equals $m^{m-2}$ if $k = n - m + 1$, and equals $0$ if $k < n - m + 1$.
The exponent $-1$ occurs only on the base $1$ (at $k = n$, and at $m = 1$), and $1^{-1} = 1$.

## Sources

- Spencer Daugherty, Pamela E. Harris, Ian Klein, and Matt McClinton, *Metered Parking Functions*, INTEGERS 25 (2025), Article A73, Lemma 4 (`integers-2025-A73-lem-4`).
