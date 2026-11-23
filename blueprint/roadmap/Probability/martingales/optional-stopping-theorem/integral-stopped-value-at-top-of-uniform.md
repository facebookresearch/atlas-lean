# General optional stopping, expectation inequality

Let $\mu$ be a probability measure,
let $(\mathcal{F}_n)_{n \in \mathbb{N}}$ be a filtration and let $(f_n)_{n \in \mathbb{N}}$ be a
real-valued submartingale with respect to $(\mathcal{F}_n)$ that is uniformly integrable. Let
$f_\infty$ be the limit process of $f$ (its almost-everywhere limit, by the martingale
convergence theorem). Then for every stopping time $\tau$ with values in
$\mathbb{N} \cup \{\infty\}$, the value $f_\tau$ of $f$ at $\tau$ (at points where
$\tau = \infty$ it is $\lim_n f_n$) satisfies
$\int f_0 \, d\mu \le \int f_\tau \, d\mu \le \int f_\infty \, d\mu$.
