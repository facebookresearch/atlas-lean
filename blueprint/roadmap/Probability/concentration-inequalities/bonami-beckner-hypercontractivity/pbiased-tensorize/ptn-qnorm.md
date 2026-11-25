# $L^q$ norm under the $p$-biased measure

For a finite set $\iota$, real $p, q$ and $f : \{0, 1\}^\iota \to \mathbb{R}$, put
$N_{p,q}(f) = \big(\mathbb{E}_p|f|^q\big)^{1/q}$, with the [$q$-th moment](ptn-qnorm-pow.md)
$\mathbb{E}_p|f|^q = \sum_\omega \prod_{i} p^{\omega_i} (1 - p)^{1 - \omega_i}\, |f(\omega)|^q$, $1/0 = 0$ and
real powers: the usual power of a positive base, $0^0 = 1$ and $0^s = 0$ for $s \ne 0$, and $x^s = |x|^s \cos(\pi s)$ for $x < 0$. A signed moment then has a real $1/q$-th power that need not be a real root: for one
coordinate, $p = 2$, $q = 3$, $f(0) = 1$ and $f(1) = 0$, the moment is $-1$ and
$N_{p,q}(f) = \cos(\pi/3) = \frac12$. For $p \in [0, 1]$ and $q \ge 1$ it is the norm $\|f\|_{L^q(\mu_p)}$ of $f$
under the $p$-biased product measure $\mu_p$. For other $p$ and $q$ it is only an algebraic extension:
the weights are signed when $p \notin [0, 1]$, and for $q = 0$ the value is $1$ for every $f$,
including $f = 0$.
