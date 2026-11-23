# First sixteen-cycle lemma for the three-term Hofstadter-like recurrence

Let $K \ge 1$ be
a natural number and let $\lambda$, $\mu_1$, $\mu_2$, $\gamma$ be integers with $\lambda > 31 + K$
and $\mu_1, \mu_2, \gamma > \lambda$. Let $a_1, \dots, a_K$ be arbitrary integers and let $B$ be
the padded three-term Hofstadter-like sequence with initial conditions
$a_1, \dots, a_K, \lambda, 7, \mu_2, 16, \mu_2, 16, \mu_1, \lambda, 7, \mu_2, 16, 2\mu_2, 16,
\mu_2, 25, \gamma, \lambda, 7$. Then for all natural numbers $k$ and $r \le 15$ with
$K + 1 \le K + 16k + r \le \lambda$, the term $B(K + 16k + r)$ is defined, and these terms are
$B(K + 16k) = \mu_1 2^{k-1} + \gamma - \mu_1$, $B(K + 16k + 1) = \lambda$, $B(K + 16k + 2) = 7$,
$B(K + 16k + 3) = \mu_2 2^k$, $B(K + 16k + 4) = 16$, $B(K + 16k + 5) = \mu_2 2^k$,
$B(K + 16k + 6) = 16$, $B(K + 16k + 7) = \mu_1 2^k$, $B(K + 16k + 8) = \lambda$,
$B(K + 16k + 9) = 7$, $B(K + 16k + 10) = \mu_2 2^k$, $B(K + 16k + 11) = 16$,
$B(K + 16k + 12) = \mu_2 2^{k+1}$, $B(K + 16k + 13) = 16$, $B(K + 16k + 14) = \mu_2 2^k$ and
$B(K + 16k + 15) = 25$.

Corrected: the paper prints $B(K + 16k + 12) = \mu_2 2^k$, which contradicts its own initial
value $B(K + 12) = 2\mu_2$; the exponent $k + 1$ matches the initial conditions and every later
term.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 6, citing the author's thesis, Proposition 9.13 (`jis-2024-24.7.4-lem-6`).
