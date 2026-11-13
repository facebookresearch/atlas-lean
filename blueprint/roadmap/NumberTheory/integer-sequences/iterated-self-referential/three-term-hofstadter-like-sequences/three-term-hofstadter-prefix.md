# Initial segment of a three-term Hofstadter-like sequence

Let $x_1, \dots, x_m$ be
integers ($m \ge 0$) and let $B$ be the padded or the unpadded three-term Hofstadter-like sequence
with initial conditions $x_1, \dots, x_m$: $B(i) = x_i$ for $1 \le i \le m$, the padded sequence
has $B(i) = 0$ for every $i \le 0$ while the unpadded one is undefined there, and for $n > m$

$$B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3)),$$

which is defined only when every value of $B$ on the right-hand side is defined and the indices
$n - B(n-1)$, $n - B(n-2)$, $n - B(n-3)$ are less than $n$. For a natural number $k$, the
initial segment is the list $B(1), \dots, B(m + k)$, the initial conditions followed by the next
$k$ terms; it is undefined when one of $B(m + 1), \dots, B(m + k)$ is undefined.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1.
