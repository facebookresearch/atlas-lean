# Upper Perron solution

For $n \in \mathbb{N}$, a set $\Omega \subseteq \mathbb{R}^n$, a function $f : \mathbb{R}^n \to \mathbb{R}$ (only its values on $\partial\Omega$ matter) and a point $x$, the upper Perron class consists of the functions $u : \mathbb{R}^n \to \mathbb{R}$ that are superharmonic on $\Omega$, bounded below on $\Omega$, and satisfy $\liminf_{\Omega \ni y \to \xi} u(y) \ge f(\xi)$ for every $\xi \in \partial\Omega$. The upper Perron solution is the extended real number

$$\overline{P}_\Omega f(x) = \inf_{u \in \mathcal{U}_f} u(x) \in [-\infty, +\infty],$$

which is $+\infty$ when the class is empty.

This is a definition for every dimension and every set; it asserts neither that the class is nonempty nor that the infimum is finite. For $n = 0$ the space is a single point and the bounded domain $\Omega = \mathbb{R}^0$ has empty boundary; no $u$ is superharmonic there (comparison with the constant harmonic function $u(x) + 1$ on $\Omega$ fails), so the value is $+\infty$.
