# Factor complexity and right-special factors of the Thue–Morse Quarto word

Let
$\mathcal{Q}$ be the Thue–Morse Quarto sequence, $p_{\mathcal{Q}}$ its factor complexity and
$\mathrm{RS}_{\mathcal{Q}}(n)$ its set of right-special factors of length $n$. Let $n \ge 16$ and
$k = \lfloor \log_2 n \rfloor$, so that $2^k \le n < 2^{k+1}$. Then
$p_{\mathcal{Q}}(n) = 13 \cdot 2^{k-2} - 2$ if $n = 2^k$,
$p_{\mathcal{Q}}(n) = 4n - 3 \cdot 2^{k-2} - 4$ if $2^k < n \le 2^k + 2^{k-1}$,
$p_{\mathcal{Q}}(n) = 3n + 3 \cdot 2^{k-2} - 3$ if $2^k + 2^{k-1} < n \le 2^k + 3 \cdot 2^{k-2}$,
and $p_{\mathcal{Q}}(n) = 2n + 5 \cdot 2^{k-1} - 2$ if $2^k + 3 \cdot 2^{k-2} < n$. Moreover
$\#\mathrm{RS}_{\mathcal{Q}}(n) = p_{\mathcal{Q}}(n+1) - p_{\mathcal{Q}}(n)$, and
$\#\mathrm{RS}_{\mathcal{Q}}(n)$ equals $4$ if $2^k < n \le 3 \cdot 2^{k-1}$, $3$ if
$3 \cdot 2^{k-1} < n \le 7 \cdot 2^{k-2}$, and $2$ if $7 \cdot 2^{k-2} < n$.

## Sources

- John M. Campbell and Benoît Cloitre, *Meta-Automatic Sequences*, Journal of Integer Sequences 29 (2026), Article 26.4.1, Proposition 33 (`jis-2026-26.4.1-prop-33`).
