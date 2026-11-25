# Stage stepping cannot cross a pinch

Consider the rectifying section of a binary distillation column with constant molar overflow, relative volatility $\alpha > 1$,
reflux ratio $R > 0$ and distillate composition $0 < x_D < 1$. Let $y_{\mathrm{eq}}(x) = \alpha x/(1 + (\alpha - 1)x)$ be the
equilibrium curve, $\ell(x) = (R x + x_D)/(R + 1)$ the operating line, and $T(x) = y_{\mathrm{eq}}^{-1}(\ell(x))$ the map from the
liquid composition on one stage to that on the next. On $[0,1]$ the inverse is
$y_{\mathrm{eq}}^{-1}(y) = y/(\alpha - (\alpha-1)y)$. The equilibrium curve, the operating line,
and the inverse all map $[0,1]$ into itself; the inverse and the operating line are strictly
increasing there, so their composition $T$ is strictly increasing there as well.

Let $0 \le x_p < x_0 \le 1$ and suppose $T(x_p) = x_p$ and $\ell(x) < y_{\mathrm{eq}}(x)$ for
$x_p < x \le x_0$. Then $x_p < T(x) < x$ for $x_p < x \le x_0$, so the stage compositions
$x_0, T(x_0), T^2(x_0), \dots$ decrease strictly and stay above $x_p$: no finite number of stages
reaches or crosses the pinch $x_p$. For $\alpha = 2$, $R = 1$ and $x_D = 3/4$, the start
$x_0 = y_{\mathrm{eq}}^{-1}(x_D) = 3/5$ lies above the fixed point $x_p = (9 - \sqrt{33})/8$.
In this example the strict comparison holds throughout $(x_p,x_0]$. Minimum-reflux formulas and
energy balances are outside this result.

## Sources

- Monica Lamm and Laura Jarboe, *Chemical Engineering Separations: A Handbook for Students*, LibreTexts, Section 1.5, the rectifying operating line, Equation 20.7, and the relative volatility, Equation 22.2, <https://eng.libretexts.org/Bookshelves/Chemical_Engineering/Chemical_Engineering_Separations%3A_A_Handbook_for_Students_(Lamm_and_Jarboe)/01%3A_Chapters/1.05%3A_Distillation>.
