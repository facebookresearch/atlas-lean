# Fractional parts of shifted Fibonacci numbers divided by $\sqrt{5}$

Let $F_n$ be the
$n$-th Fibonacci number, with $F_0 = 0$ and $F_1 = 1$, let $\varphi = (1 + \sqrt{5})/2$ be the
golden ratio, so that $2\varphi - 1 = \sqrt{5}$, and write $\{y\} = y - \lfloor y \rfloor$ for the
fractional part. Let $n \ge 13$ be a natural number and $\varepsilon \in \{-4, 0, 4\}$, let
$c_{n,\varepsilon}$ be Wesley's constant, which depends on $n \bmod 4$ and $\varepsilon$, and put
$y = (F_n + \varepsilon)/(2\varphi - 1)$. Then
(i) $\{y\} = -2(-\varphi)^{-n}/5 + c_{n,\varepsilon}$, and
(ii) $\lfloor y \rfloor$ is even if and only if $\varepsilon = 0$ and
$n \equiv 0, 1, 2, 3, 5, 10 \pmod{12}$, or $\varepsilon = 4$ and
$n \equiv 0, 2, 3, 9, 10 \pmod{12}$, or $\varepsilon = -4$ and
$n \equiv 0, 1, 2, 5, 7, 10, 11 \pmod{12}$.

The paper prints $+2(-\varphi)^{-n}/5$ in (i). The sign $-$ is the one its proof derives
(Equation (1)); the printed sign fails for every $n \ge 13$, since this term is nonzero.

## Sources

- William J. Wesley, *Improved Ramsey-Type Theorems for Fibonacci Numbers and Other Sequences*, INTEGERS 25 (2025), Article A29, Lemma 5 (`integers-2025-A29-lem-5`).
