# Strain of a bar fixed at one end under an end force and a load

For real numbers $k$, $L$, $P$ and $x$ and a function $f \colon \mathbb{R} \to \mathbb{R}$, the
load-path strain is

$$\varepsilon(x) = \frac{1}{k}\left(P + \int_x^L f(y)\, dy\right).$$

The integral is oriented ($\int_x^L = -\int_L^x$ when $x > L$) and is $0$ when $f$ is not integrable
on the interval between $x$ and $L$; with the convention $a/0 = 0$, $\varepsilon = 0$ when $k = 0$.
In the model $k > 0$, $L > 0$, $f$ is continuous on $[0, L]$ and $x \in [0, L]$: then
$P + \int_x^L f$ is the internal axial force at $x$, the end force plus the load carried between $x$
and $L$ ([load path](axial-force-eq.md)), and $\varepsilon$ is the derivative of every solution of
the [fixed-traction problem](is-fixed-traction-solution.md).
