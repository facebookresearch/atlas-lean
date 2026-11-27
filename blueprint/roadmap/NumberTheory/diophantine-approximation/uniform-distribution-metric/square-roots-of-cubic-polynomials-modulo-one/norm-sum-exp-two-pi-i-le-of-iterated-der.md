# Second-derivative test for exponential sums

Let $a < b$ be integers, let $\rho > 0$,
and let $f : \mathbb{R} \to \mathbb{R}$ be twice continuously differentiable, with either
$f''(t) \ge \rho$ for every $t \in [a, b]$ or $f''(t) \le -\rho$ for every $t \in [a, b]$. Then

$$\Bigl|\sum_{n=a}^{b} e(f(n))\Bigr| \le \bigl(|f'(b) - f'(a)| + 2\bigr)
\Bigl(\frac{4}{\sqrt{\rho}} + 3\Bigr),$$

where $e(x) = e^{2\pi i x}$.

Here $f$ is $C^2$ on all of $\mathbb{R}$; every $C^2$ function on $[a, b]$ extends to one, so
this loses nothing.

## Sources

- Anji Dong, Katerina Saettone, Kendra Song and Alexandru Zaharescu, *An Equidistribution Result for Differences Associated with Square Pyramidal Numbers*, Journal of Integer Sequences 29 (2026), Article 26.5.5, Lemma 4 (`jis-2026-26.5.5-lem-4`), quoted there from Kuipers and Niederreiter, *Uniform Distribution of Sequences*, Thm. 2.7.
