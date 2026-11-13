# Characterization of minimal permutations with a given number of descents

Let $\sigma$ be a
permutation of $\{1, \dots, n\}$ and let $d$ be a natural number. A descent of a permutation
$\tau$ of $\{1, \dots, k\}$ is an index $1 \le i \le k - 1$ with $\tau(i+1) < \tau(i)$, and $\tau$
occurs in $\sigma$ if there are positions $\varphi(1) < \dots < \varphi(k)$ in $\{1, \dots, n\}$
with $\tau(a) < \tau(b)$ exactly when $\sigma(\varphi(a)) < \sigma(\varphi(b))$. Then $\sigma$ has
exactly $d$ descents and no permutation $\tau$ of $\{1, \dots, k\}$ with $0 < k < n$ occurring in
$\sigma$ has exactly $d$ descents if and only if $\sigma$ has exactly $d$ descents and every
ascent $i$ of $\sigma$ (an index $1 \le i \le n - 1$ with $\sigma(i) < \sigma(i+1)$) satisfies
$2 \le i \le n - 2$ and either $\sigma(i) < \sigma(i-1) < \sigma(i+2) < \sigma(i+1)$ or
$\sigma(i) < \sigma(i+2) < \sigma(i-1) < \sigma(i+1)$; that is, the entries at positions
$i-1, i, i+1, i+2$ form the pattern $2143$ or $3142$.

## Sources

- Stefano Bilotta, Elisabetta Grazzini, and Elisa Pergola, "Enumeration of Two Particular Sets of Minimal Permutations", Journal of Integer Sequences 18 (2015), Article 15.10.2, Theorem `thm:characterization`, lines 230-237, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Grazzini/graz3.tex>.
