# Superexponential tightness

Let $(\mu_n)$ be finite measures on a Polish space satisfying the large deviation principle with a
good rate function $I$. Then for every $\ell \in \mathbb{R}$ there is a compact set $K_\ell$ with

$$\mu_n(K_\ell^{c}) \le e^{-n \ell} \quad \text{for every } n.$$

This is the large deviation analogue of Prokhorov's tightness condition, and the reason a good
rate function lets one reduce upper bounds to compact sets. Varadhan's proof covers the compact
sub-level set $\{I \le \ell + 2\}$, for each $k$, by finitely many balls of radius $1/k$; the upper
bound on the complement of their union gives mass at most $e^{-k} e^{-n\ell}$ for large $n$, the
finitely many remaining measures are tight individually, and the intersection over $k$ is totally
bounded, hence has compact closure in the complete space.

## Sources

- S. R. S. Varadhan, *Large Deviations*, lecture notes, New York University, Spring 2010, Section 2, Theorem 2.4 and Remark 2.5 (https://math.nyu.edu/~varadhan/LDP/1-2.pdf).
