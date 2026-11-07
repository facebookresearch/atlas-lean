# Total symmetric peak height over compositions with a fixed number of parts

For
$n, k \ge 0$ let $\mathrm{hsp}(n, k)$ be the sum, over all compositions $c$ of $n$ with exactly
$k$ parts, of the symmetric peak height sum of the sequence of parts of $c$. If $k > 3$, then
for every $n \ge 0$

$$
\mathrm{hsp}(n, k) = (k - 2) \sum_{m=2}^{n-k+1} \sum_{b=1}^{\min(m-1,\, t_m)}
\binom{n - 2b - m - 1}{k - 4} (m - b),
\qquad t_m = \left\lfloor \frac{n - m - k + 3}{2} \right\rfloor,
$$

where an empty sum is $0$.

## Sources

- Walaa Asakly and Noor Kezil, *The Heights of Symmetric Peaks and the Depths of Symmetric Valleys over Compositions of an Integer*, INTEGERS 26 (2026), Article A65, Theorem 2(a) (`integers-2026-A65-thm-2`).
