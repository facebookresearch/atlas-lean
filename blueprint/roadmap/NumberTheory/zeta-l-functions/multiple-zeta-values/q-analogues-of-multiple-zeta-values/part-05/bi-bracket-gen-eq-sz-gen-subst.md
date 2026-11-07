# Translation between bi-brackets and the Schlesinger–Zudilin model

Let $r$ be a natural
number, let $g(X_1, \dots, X_r; Y_1, \dots, Y_r)$ be the generating series of bi-brackets of depth
$r$ and $s(X_1, \dots, X_r; Y_1, \dots, Y_r)$ the generating series of Schlesinger–Zudilin qMZVs of
depth $r$, both power series in the $2r$ variables over $\mathbb{Q}[[q]]$. For a power series $Z$
without constant term, write $e^Z$ and $\ln(1 + Z)$ for the substitution of $Z$ into the
exponential series and into $\ln(1 + T) = \sum_{n \ge 1} (-1)^{n+1} T^n / n$, and put
$S_j = Y_1 + \dots + Y_j$. Then:

(i) $\prod_{j=1}^r e^{X_j} e^{S_j} \cdot s(e^{X_1} - 1, \dots, e^{X_r} - 1; e^{S_1} - 1, \dots,
e^{S_r} - 1) = g(X_1, \dots, X_r; Y_1, \dots, Y_r)$;

(ii) $\prod_{j=1}^r (1 + X_j)(1 + Y_j) \cdot s(X_1, \dots, X_r; Y_1, \dots, Y_r)$ equals
$g(\ln(1 + X_1), \dots, \ln(1 + X_r); \ln(1 + Y_1), \ln(1 + Y_2) - \ln(1 + Y_1), \dots,
\ln(1 + Y_r) - \ln(1 + Y_{r-1}))$.

Part (ii) is stated with the unit $\prod_j (1 + X_j)(1 + Y_j)$ multiplied out instead of inverted.

## Sources

- Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6, Theorem 13 (translation bi-brackets/SZ model) (`integers-2024-A6-thm-13`).
