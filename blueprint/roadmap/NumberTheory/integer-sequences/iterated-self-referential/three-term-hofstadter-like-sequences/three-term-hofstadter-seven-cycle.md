# Seven-cycle lemma for the three-term Hofstadter-like recurrence

Let $K$, $c$ and
$\gamma$ be natural numbers with $K \ge 7$, $c \ge 1$, $\gamma \le 6$ and $7c + \gamma \le K$, and
put $L = K - 7c - \gamma$ and $M = K + L + 5$. For a tuple $(t_0, \dots, t_6)$ write
$(t_0, \dots, t_6)_\gamma$ for its entry $t_\gamma$. Let $\lambda$ and $\mu$ be integers with
$\lambda \ge -2c + (2, 1, 4, 3, 2, 1, 0)_\gamma$ and $\mu \ge -c + (0, 0, 3, 2, 1, 0, -1)_\gamma$,
and put $\nu = (-2, -2, 2, 1, 0, -1, -2)_\gamma$. Let $a_1, \dots, a_L$ be arbitrary integers and
let $B$ be the padded three-term Hofstadter-like sequence with initial conditions
$1, 2, \dots, K, 6, a_1, \dots, a_L, 2K + \lambda - 2, 2K + \mu - 1, K - 2$. Then for every
integer $k$ and every $r \in \{0, 1, \dots, 6\}$ with $M - 3 \le M + 7k + r \le 2K + \nu$, the
term $B(M + 7k + r)$ is defined, and these terms are $B(M + 7k) = L + 7k + 7$,
$B(M + 7k + 1) = M + 7k + 2$, $B(M + 7k + 2) = M + 7k + 4$, $B(M + 7k + 3) = 7$,
$B(M + 7k + 4) = 2K + 2k + \lambda$, $B(M + 7k + 5) = 2K + k + \mu$ and $B(M + 7k + 6) = K - 2$.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Lemma 3 (`jis-2024-24.7.4-lem-3`).
