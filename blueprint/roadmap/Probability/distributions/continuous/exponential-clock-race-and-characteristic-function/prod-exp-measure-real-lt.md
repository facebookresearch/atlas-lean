# Two competing exponential clocks

Write $\mathrm{Exp}(r)$ for the exponential law of rate $r$, with density $r e^{-r x}$ on $[0, \infty)$. Let $a, b > 0$. Under the product law $\mathrm{Exp}(a) \otimes \mathrm{Exp}(b)$ on $\mathbb{R}^2$,

$$(\mathrm{Exp}(a) \otimes \mathrm{Exp}(b))\bigl(\{(x, y) : x < y\}\bigr) = \frac{a}{a + b}.$$

Equivalently, for a probability space $(\Omega, \mu)$ and independent random variables $X, Y : \Omega \to \mathbb{R}$ with laws $X \sim \mathrm{Exp}(a)$ and $Y \sim \mathrm{Exp}(b)$ ($X$ and $Y$ a.e. measurable with these pushforward laws),

$$\mu(\{\omega : X(\omega) < Y(\omega)\}) = \frac{a}{a + b}:$$

the joint law of $(X, Y)$ is the product law, and the coordinate projections on the product recover the first form. So of two independent exponential clocks, the first rings first with probability $a / (a + b)$; this is the case of two clocks in the [race of competing exponential clocks](../exponential-distribution/competing-exponential-clocks.md).
