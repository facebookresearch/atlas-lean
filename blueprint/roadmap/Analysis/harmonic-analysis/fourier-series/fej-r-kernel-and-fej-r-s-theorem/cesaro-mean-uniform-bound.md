# Quantitative Fejér theorem

Let $T > 0$, let $f$ be a continuous complex-valued function
on the circle $\mathbb{R}/T\mathbb{Z}$, and write $\sigma_N f$ for its $N$-th Cesàro–Fourier
mean. Let $\varepsilon > 0$ and $\delta > 0$ be such that $|f(a) - f(b)| < \varepsilon / 2$ for
all points $a, b$ of the circle at distance less than $\delta$. Then there is
$N_0 \in \mathbb{N}$ such that $|f(x) - \sigma_N f(x)| < \varepsilon$ for every $N \ge N_0$ and
every point $x$ of the circle.

The proof writes $f(x) - \sigma_N f(x) = \int K_N(t)\,(f(x) - f(x - t))\,dt$, where $K_N$ is the
$N$-th Fejér kernel and the integral is against the Haar probability measure, and splits it
into the points $t$ at distance less than $\delta$ from $0$, where $f(x) - f(x - t)$ is small,
and the remaining points, where the Fejér kernel is $O(1/((N+1)\delta^2))$.
