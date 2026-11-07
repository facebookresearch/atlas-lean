# Three-term Hofstadter-like sequence

Let $x_1, \dots, x_m$ be integers ($m \ge 0$), the
initial conditions, and choose whether the sequence is padded. The sequence $B$ has $B(i) = x_i$
for $1 \le i \le m$; the padded sequence has $B(i) = 0$ for every integer $i \le 0$, while the
unpadded one is undefined at every $i \le 0$. For $n > m$,

$$B(n) = B(n - B(n-1)) + B(n - B(n-2)) + B(n - B(n-3)),$$

which is defined only when every value of $B$ on the right-hand side is defined and the indices
$n - B(n-1)$, $n - B(n-2)$, $n - B(n-3)$ are less than $n$; once a term is undefined, the
sequence stops and every later term is undefined. The term at a natural number index $j$ is
$B(j)$ when this is defined and undefined otherwise; in particular the term at index $0$ is $0$
for the padded sequence and undefined for the unpadded one.

## Sources

- Nathan Fox, *The Behavior of a Three-Term Hofstadter-Like Recurrence with Linear Initial Conditions*, Journal of Integer Sequences 27 (2024), Article 24.7.4, Section 1.
