# Paris-law crack growth, power branch: $(a_0^r + rKN)^{1/r}$

For real numbers $r$, $K$, $a_0$ and $N$, the power-branch Paris crack length after $N$ cycles is

$$a(N) = \bigl(a_0^r + r K N\bigr)^{1/r},$$

with real powers. It is meant as the solution, with $a(0) = a_0$, of the reduced Paris law
$da/dN = K a^{m/2}$ for a growth exponent $m \ne 2$, where $r = 1 - m/2 \ne 0$. The reduced law
comes from the Paris law $da/dN = C (\Delta K)^m$ with stress-intensity range
$\Delta K = Y \Delta\sigma \sqrt{\pi a}$ for a constant geometry factor $Y$ and fatigue stress range
$\Delta\sigma$, so that $K = C (Y \Delta\sigma \sqrt{\pi})^m$ is an aggregate growth coefficient,
not a stress intensity.

The solution reading needs $K > 0$, $a_0 > 0$ and a positive base $B(N) = a_0^r + r K N$; for
$r < 0$ ($m > 2$) the base vanishes at the blow-up cycle count $N^* = a_0^r / (-rK)$. For $r \ne 0$
the formula [solves the reduced Paris law](has-deriv-at-paris-crack-pow.md) wherever the base is
positive, for all real $K$ and $a_0$, and for $a_0 > 0$ it
[starts at $a_0$](paris-crack-pow-zero.md).

The formula accepts every real input, with the conventions $0^t = 0$ for $t \ne 0$, $s^0 = 1$ and
$s^t = |s|^t \cos(\pi t)$ for $s < 0$ (these also give $a_0^r$ for $a_0 \le 0$). For $r \ne 0$ it is
$0$ where $B(N) = 0$, so for $r < 0$ its value at the blow-up count $N^*$ is $0$, and it is
$|B(N)|^{1/r} \cos(\pi / r)$ where $B(N) < 0$. For $r = 0$, with the convention $0^{-1} = 0$, it is
$1$ for every $N$.