# Product identities for calibrating numbers

Let $a$ and $d$ be positive integers and let
$k \ge 1$. Put $\alpha = (a + d)/d$, and let $n_i = 1 + \alpha^{2^{i-1}}$ for $1 \le i < k$ and
$n_k = \alpha^{2^{k-1}}$ (the calibrating numbers for $a/(a + d)$). Then
$\prod_{i=1}^{k} (1 - 1/n_i) = a/(a + d)$; for every $j$ with $1 \le j < k$,
$\prod_{i=1}^{j} n_i = (d/a)(\alpha^{2^j} - 1)$; and
$\prod_{i=1}^{k} n_i = (d/a)(\alpha^{2^k} - \alpha^{2^{k-1}})$.

## Sources

- Andrew Stone, *Improved Upper Bounds for Odd Perfect Numbers -- Part I*, INTEGERS 24 (2024), Article A114, Lemma 3.
