# Alternating series with a three-step continued fraction pattern

Let $(u_i)_{i \ge 0}$
be positive integers with $u_0 = 1$, and let $x$ be an irrational real number with
$\sum_{i \ge 0} (-1)^i / u_i = x$. Write $x = [a_0; a_1, a_2, \dots]$ for its continued fraction
expansion and $p_n / q_n = [a_0; a_1, \dots, a_n]$ for its convergents, with $q_0 = 1$ and
$q_1 = a_1$. Suppose that for every $n \ge 0$ we have
$\sum_{i=0}^{n} (-1)^i / u_i = p_{n+1} / q_{n+1}$, $u_{3n+2} \mid u_{3n+3}$,
$u_{3n+2} - u_{3n+1} = \bigl(\prod_{j=0}^{\lfloor 3n/2 \rfloor} u_{3n-2j+1} / u_{3n-2j}\bigr)^2$
and $u_{3n+4} - u_{3n+3} = (u_{3n+3} / u_{3n+2})^2 (u_{3n+2} - u_{3n+1})$. Then
(i) $u_n = q_n q_{n+1}$ for every $n \ge 0$, (ii) for every $n \ge 0$ there is a natural number
$m$ with $a_{3n+4} = m \, q_{3n+2}$, and (iii) $a_{3n+3} = 1$ for every $n \ge 0$ and
$a_{3n+2} = 1$ for every $n \ge 1$.

The product runs over the quotients $u_{k+1} / u_k$ for $k = 3n, 3n - 2, 3n - 4, \dots$, ending
at $k = 1$ when $n$ is odd and at $k = 0$ when $n$ is even. The condition $a_{3n+2} = 1$ is
stated only for $n \ge 1$, because it can fail at $n = 0$: the continued fraction
$[0; 1, 2, 1, 3, 1, 1, 19, 1, 1, 699, \dots]$ with $u_n = q_n q_{n+1}$ satisfies every hypothesis
and has $a_2 = 2$.

## Sources

- Khalil Ayadi, Chiheb Ben Bechir, and Maher Saadaoui, *Continued Fractions with Predictable Patterns and Transcendental Numbers*, Journal of Integer Sequences 28 (2025), Article 25.1.4, Theorem 10 (`jis-2025-25.1.4-thm-10`).
