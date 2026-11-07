# Entry 22 of Chapter 9 of Ramanujan's notebooks

For real $u$ and $k \ge 0$ let
$T_k(u) = \frac{2^{2k} (k!)^2 \sin^{2k+2} u}{(2k+1)! \, (2k+2)^2}$. Let $x$ be real with
$0 \le x \le \pi/4$. Then $2 \cos x > 0$, the series $\sum_{j \ge 0} \frac{1}{(2j+1)^3}$,
$\sum_{k \ge 0} \bigl(T_k(x) + T_k(\pi/2 - x)\bigr)$,
$\sum_{k \ge 0} \frac{\binom{2k}{k} \cos^{2k+1} x}{2^{2k} (2k+1)^2}$ and $\sum_{k \ge 0} T_k(2x)$
converge absolutely, and

$$
\sum_{k \ge 0} \bigl(T_k(x) + T_k(\pi/2 - x)\bigr) = -\frac{\pi^2}{8} \log(2 \cos x) +
\frac{\pi}{2} \sum_{k \ge 0} \frac{\binom{2k}{k} \cos^{2k+1} x}{2^{2k} (2k+1)^2} +
\frac{1}{4} \sum_{k \ge 0} T_k(2x) - \frac{1}{2} \sum_{j \ge 0} \frac{1}{(2j+1)^3}.
$$

Proof: Differentiate the factorial and central-binomial series termwise, reduce
the logarithmic integral by Abel's limit and dominated convergence, and finish
by the fundamental theorem of calculus. This follows Berndt's Entries 20–23 and
Lehmer's arcsine series.

## Sources

- Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9, Entry 22, pp. 270–271. The printed range `0 ≤ x ≤ π / 2` is false. This target uses `0 ≤ x ≤ π / 4`, the range supported by the source proof's substitution of `2 * x` into Entry 20; the endpoint remains an explicit proof obligation.
