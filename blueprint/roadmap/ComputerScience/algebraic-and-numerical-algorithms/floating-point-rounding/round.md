# Rounding in a bounded format

Let $p$ be a natural number, $q_{\min}$ an integer and $r$ a
rounding mode. For $x$ in a linearly ordered field with a floor function, let
$e = \max(\lfloor \log_2 |x| \rfloor - (p - 1), q_{\min})$, where
$\lfloor \log_2 |x| \rfloor$ is the largest integer $n$ with $2^n \le |x|$ for $x \ne 0$ and is
$0$ for $x = 0$. The rounding of $x$ in mode $r$ is $R_r(x / 2^e) \cdot 2^e$, where $R_r$ rounds
to an integer in mode $r$: scale $x$ so that the last place of its $p$-bit significand, but no
place below $2^{q_{\min}}$, is the units digit, round to an integer in the mode, and scale back.

Capping $e$ below at $q_{\min}$ gives gradual underflow. For $p \ge 1$ and
$|x| < 2^{q_{\min} + p - 1}$, the smallest normal number, the result is a multiple of $2^{q_{\min}}$
of absolute value at most $2^{q_{\min} + p - 1}$: zero, a subnormal number, or
$\pm 2^{q_{\min} + p - 1}$ itself. The exponent is not bounded above, so the result can exceed the
largest finite number; in the mode to nearest and for $|x| \ge 2^{q_{\min} + p - 1}$, this is
$\mathrm{fl}_p(x)$.

## Sources

- Boldo, Jourdan, Leroy and Melquiond, *Verified compilation of floating-point computations*, Journal of Automated Reasoning 54(2), 2015, Section 5.2 (Flocq's rounding, with no upper bound on the exponent).
