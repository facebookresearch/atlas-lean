# Importance sampling is unbiased

Let $\mu$ be a measure on $\Omega$, let $\rho$ be a
measure on $\alpha$, let $w : \alpha \to [0, \infty]$ be measurable with $w < \infty$
$\rho$-almost everywhere, and let $\nu$ be the measure with density $w$ with respect to $\rho$.
Let $f : \alpha \to \mathbb{R}$ be measurable and integrable with respect to $\nu$. If
$X_0, X_1, \ldots : \Omega \to \alpha$ are measurable and the pushforward of $\mu$ along each
$X_i$ is $\rho$, then for every $n \ne 0$ the integral with respect to $\mu$ of the
importance-sampling estimate of $f$ with weight $w$ from the first $n$ samples equals
$\int f \, d\nu$.
