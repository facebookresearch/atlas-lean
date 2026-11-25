# Wasserstein distance of order $p$

Let $(X, d)$ be an extended metric space with a σ-algebra and let $\mu, \nu$ be probability measures
on $X$. The Wasserstein distance of order $p$ is

$$W_p(\mu, \nu) = \Bigl(\inf_{\pi} \int_{X \times X} d(x, y)^p \, d\pi(x, y)\Bigr)^{1/p} \in [0, \infty],$$

the infimum over all couplings $\pi$ of $\mu$ and $\nu$; that is, $W_p = C_p^{1/p}$ for the
[optimal transport cost](transport-cost.md) $C_p$. Villani defines it for a Polish metric space and
$p \in [1, \infty)$. The formula $W_p = C_p^{1/p}$ is taken for every real $p$ and every pseudo-extended
metric space, with the conventions of real powers in $[0, \infty]$ ($t^0 = 1$; $0^r = \infty$ and
$\infty^r = 0$ for $r < 0$) and $1/0 = 0$, so that $W_0 = C_0^0 = 1$; the results state the
hypotheses they need. $W_1$ is also called the Kantorovich–Rubinstein
distance.

$W_p$ may be infinite; it is [finite](wasserstein-lt-top.md) on the Wasserstein space $P_p(X)$ of
measures with a finite $p$-th moment (Villani, Definition 6.4).

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Definition 6.1 and Particular Case 6.2.
