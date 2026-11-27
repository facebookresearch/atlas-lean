# Cauchy's estimate for the coefficients of the Cauchy power series

Let $E$ be a complex normed space, $f \colon \mathbb{C} \to E$ a function, $c \in \mathbb{C}$, $R$ a real
number and $n \ge 0$, and let $p_n$ be the $n$-th coefficient of the Cauchy power series of $f$ on the
circle $\theta \mapsto c + R e^{i\theta}$, the continuous $n$-linear map

$$p_n(v_1, \dots, v_n) = v_1 \cdots v_n \cdot \frac{1}{2 \pi i} \oint \frac{f(w)}{(w - c)^{n+1}} \, dw$$

with the integral over that circle. Then its operator norm satisfies

$$\lVert p_n \rVert \le \Bigl(\frac{1}{2\pi} \int_0^{2\pi} \lVert f(c + R e^{i\theta}) \rVert \, d\theta\Bigr) \, |R|^{-n}.$$

No hypothesis on $f$ or completeness of $E$ is needed, with the conventions that an $E$-valued integral
is $0$ when the integrand is not integrable or when $E$ is not complete, and that $|R|^{-1} = 0$ when
$R = 0$. If $\theta \mapsto \lVert f(c + R e^{i\theta}) \rVert$ is not integrable, Mathlib assigns the
real-valued integral on the right the value $0$; completeness of $E$ does not affect that integral. In
particular, if
$\lVert f(w) \rVert \le M$ on the circle $|w - c| = R$ with $R > 0$, then $\lVert p_n \rVert \le M R^{-n}$.

## Sources

- Mathlib, `norm_cauchyPowerSeries_le` in `Mathlib.MeasureTheory.Integral.CircleIntegral`, at the pinned
  commit <https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/MeasureTheory/Integral/CircleIntegral.lean#L651-L653>.
- L. V. Ahlfors, Complex Analysis, 3rd ed., Ch. 4, §2.3 (higher derivatives and Cauchy's estimate).
