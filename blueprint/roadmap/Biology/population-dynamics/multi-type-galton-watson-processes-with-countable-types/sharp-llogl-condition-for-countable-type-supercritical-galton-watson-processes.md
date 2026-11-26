# Sharp $L\log L$ condition for countable-type supercritical Galton–Watson processes

**Setting.** Let $(Z(n))$ be a multi-type Galton–Watson process on a countable type set $\mathcal X$; an individual of type $x$ has offspring vector $L^{(x)}$ with mean matrix $M_{xy} = \mathbb E[L^{(x)}_y]$. Assume $M$ is irreducible, aperiodic and recurrent with finite Perron value $\varrho > 1$ and right/left eigenvectors $h, \tilde h$ (so $\varrho$ is a simple largest eigenvalue), and that $\langle Z(0), h\rangle < \infty$. The additive martingale $W_n = \varrho^{-n}\langle Z(n), h\rangle$ converges a.s. to $W$. The *spinal chain* $X$ on $\mathcal X$ has transitions $p_{xy} = M_{xy}h_y/(\varrho h_x)$ and stationary vector $\pi_x = \tilde h_x h_x$; given $X$, let $Y_n$ be independent with the law of $\langle L^{(x)}, h\rangle$ size-biased by $L^{(x)}_y$ when $(X_{n-1}, X_n) = (x, y)$.

**Theorem.** Fix a type $x$ and let $T_1 = \inf\{k \ge 1 : X_k = x\}$. If $M$ is positive recurrent, then
$$\mathbb E_x\!\left[\log_+\Bigl(\sum_{k=1}^{T_1}\varrho^{-k}Y_k\Bigr)\right] < \infty$$
is equivalent to each of: (i) $\mathbb E[W] = \langle Z(0), h\rangle$ (uniform integrability of $(W_n)$); (ii) $\mathbb P(W > 0) > 0$; (iii) $\{W = 0\}$ coincides a.s. with local extinction $\{Z_y(n) \to 0 \ \forall y\}$. The simpler uniform condition $\sum_x \tilde h_x\,\mathbb E[\langle L^{(x)}, h\rangle\log_+\langle L^{(x)}, h\rangle] < \infty$ is sufficient but not necessary. In the positive recurrent case with $\mathbb P(W > 0) > 0$, the normalized type distribution $\varrho^{-n}Z(n)$ converges to $W\,\tilde h$ in $L^1$, while in the null recurrent case $\varrho^{-n}\mathbb E[Z_x(n)] \to 0$.

## Expansion

This is a Kesten–Stigum theorem for infinitely many types, allowing infinite total population in each generation as long as $\langle Z(n), h\rangle$ is finite. The proof uses the spine decomposition: under the size-biased measure $W_n$ is a sum over the spine of the $h$-weighted sizes of sibling subtrees, discounted by $\varrho^{-k}$. Positive recurrence lets one cut the spine into i.i.d. excursions between returns to $x$, so $W_n$ stays bounded iff the log-moment of one excursion's contribution is finite (the classical $\log$ criterion for perpetuities), which is the sharp condition above. Countable type spaces arise for branching populations structured by an unbounded trait such as age, mutation load or telomere length.

## Sources

- M. André and J.-J. Duchamps, "Sharp $L \log L$ condition for supercritical Galton-Watson processes with countable types", arXiv:2503.05575 (2025), Proposition 1, Theorems 2 and 6, Propositions 13–14, <https://doi.org/10.48550/arXiv.2503.05575>.
