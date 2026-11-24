# The Halfin–Whitt limit for integer and rounded server numbers

Let $\beta > 0$ and let $s_a$ be positive integers with $s_a > a$ and $(s_a - a)/\sqrt a \to \beta$ as $a \to \infty$, for instance $s_a = \lceil a + \beta\sqrt a\,\rceil$ or, for large $a$, $\lfloor a + \beta\sqrt a\rfloor$. Then the Erlang-C delay probability $C(s_a, a)$ of the M/M/$s_a$ queue with offered load $a$ converges to $\theta(\beta) = \big(1 + \beta\Phi(\beta)/\varphi(\beta)\big)^{-1}$; equivalently $\sqrt{s_a}\,(1 - a/s_a) \to \beta$ suffices.

Proof. Let $0 < \varepsilon < \beta$. For large $a$, $a + (\beta - \varepsilon)\sqrt a \le s_a \le a + (\beta + \varepsilon)\sqrt a$, so by monotonicity in the number of servers (extended to real numbers of servers, which agrees with Erlang C at integers) $C(a + (\beta+\varepsilon)\sqrt a, a) \le C(s_a, a) \le C(a + (\beta-\varepsilon)\sqrt a, a)$. The two bounds tend to $\theta(\beta + \varepsilon)$ and $\theta(\beta - \varepsilon)$, and $\theta$ is continuous on $(0, \infty)$, so letting $\varepsilon \to 0$ gives the limit. The equivalence holds because $\sqrt{s_a}(1 - a/s_a) = (s_a - a)/\sqrt{s_a}$ and $s_a/a \to 1$.

## Depends on

- [The Erlang-C delay probability and the mean wait in the M/M/s queue](erlang-c-delay-probability-and-mean-wait.md): the Erlang-C delay probability.

## Proof depends on

- [The Erlang C formula for a real number of servers](erlang-c-for-real-server-numbers.md): agreement with Erlang C at integers, monotonicity in the number of servers, and the real-server limit.

## Sources

- A. J. E. M. Janssen, J. S. H. van Leeuwaarden and B. Zwart, 'Refining square root staffing by expanding Erlang C', *Operations Research* 59(6), 2011 (preprint), Section 2, equation (2.1), <https://nuhagphp.univie.ac.at/janssen/data/p166.pdf>. The source states a special case or part of the statement; the rest is derived on this page.
