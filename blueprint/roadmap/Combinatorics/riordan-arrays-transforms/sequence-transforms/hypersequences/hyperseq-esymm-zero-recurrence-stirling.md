# Elementary symmetric functions of the first integers via Stirling numbers

For
$j, k \in \mathbb{N}$ let $e_{j,k}$ be the elementary symmetric polynomial of degree $k$ evaluated
at $1, 2, \dots, j$ (the source's $e_{j,k}(0)$), and let $c(j, i)$ be the unsigned Stirling number
of the first kind. Then $e_{0,k} = 1$ if $k = 0$ and $e_{0,k} = 0$ otherwise; for all $j, k$,
$e_{j+1,k+1} = e_{j,k+1} + (j + 1)\, e_{j,k}$; and for all $k \le j$,

$$e_{j,k} = \sum_{\ell=0}^{k} \binom{j-k+\ell}{\ell}\, c(j, j-k+\ell) = c(j + 1, j + 1 - k).$$

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*, INTEGERS 26 (2026), Article A36, Corollary 3.
