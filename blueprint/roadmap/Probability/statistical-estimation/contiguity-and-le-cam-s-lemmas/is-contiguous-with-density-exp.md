# Le Cam's first lemma

Let $(\Omega, P)$ be a probability space, $h \in \mathbb{R}$, $v \ge 0$, and $\Lambda_n, S_n : \Omega \to \mathbb{R}$ with each $\Lambda_n$ measurable, such that the measures $Q_n$ with density $e^{\Lambda_n}$ with respect to $P$ are probability measures. Assume that $S_n \to N(0, v)$ in distribution under $P$ and that $\Lambda_n - h S_n \to -h^2 v/2$ in $P$-probability. Then $(Q_n)$ is [contiguous](is-contiguous.md) with respect to the constant sequence $(P)$.

This is the locally asymptotically normal case of Le Cam's first lemma, in which $\Lambda_n \to N(-\sigma^2/2, \sigma^2)$ under $P$ with $\sigma^2 = h^2 v$; the general form (any limit $L$ of $dQ_n/dP$ with $\mathbb{E} L = 1$) is not part of this statement.

## Sources

- L. Le Cam, *Locally asymptotically normal families of distributions*, Univ. California Publ. Statist. 3 (1960), 37–98.
- A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Lemma 6.4 and Example 6.5.
