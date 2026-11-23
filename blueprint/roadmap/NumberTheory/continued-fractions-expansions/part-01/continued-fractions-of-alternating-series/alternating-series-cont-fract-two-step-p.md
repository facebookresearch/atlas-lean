# Alternating series with a two-step continued fraction pattern

Let $(u_i)_{i \ge 0}$ be
positive integers with $u_0 = 1$, and let $x$ be an irrational real number with
$\sum_{i \ge 0} (-1)^i / u_i = x$. Write $x = [a_0; a_1, a_2, \dots]$ for its continued fraction
expansion and $p_n / q_n = [a_0; a_1, \dots, a_n]$ for its convergents, with $q_0 = 1$ and
$q_1 = a_1$. Suppose that for every $n \ge 0$ we have
$\sum_{i=0}^{n} (-1)^i / u_i = p_{n+1} / q_{n+1}$, $u_{2n+1} \mid u_{2n+2}$ and
$u_{2n+3} = \bigl(\prod_{j=0}^{n} u_{2j+2} / u_{2j+1}\bigr)^2 + u_{2n+2}$. Then
(i) $u_n = q_n q_{n+1}$ for every $n \ge 0$, (ii) for every $n \ge 0$ there is a natural number
$m$ with $a_{2n+3} = m \, q_{2n+1}$, and (iii) $a_{2n+2} = 1$ for every $n \ge 1$.

Part (iii) is stated only for $n \ge 1$, because it can fail at $n = 0$: the continued fraction
$[0; 1, 2, 1, 1, 4, 1, 32, 1, 1280, \dots]$, continued by $a_{2n+4} = 1$ and
$a_{2n+3} = q_{2n+1}$, with $u_n = q_n q_{n+1}$ (here $q = 1, 1, 3, 4, 7, 32, 39, 1280, \dots$)
satisfies every hypothesis and has $a_2 = 2$.

## Sources

- Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.4, Theorem 4 (`jis-2025-25.1.4-thm-4`).
