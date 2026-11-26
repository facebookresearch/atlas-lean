# Chi-square contraction and pointwise transition bounds for reversible chains

Let $P$ be reversible with respect to $\pi$ on a finite set, with $\pi(x) > 0$ for all $x$, contraction factor $\lambda_\ast$, and Pearson divergence $\chi^2(\nu \| \pi) = \sum_x \nu(x)^2/\pi(x) - 1$. Then for every distribution $\nu$, all states $x, y$ and all $t \ge 0$:

1. $\chi^2(\nu P^t \| \pi) \le \lambda_\ast^{2t}\, \chi^2(\nu \| \pi)$, so $\chi^2(P^t(x,\cdot)\|\pi) \le \lambda_\ast^{2t}(1-\pi(x))/\pi(x)$;
2. $\bigl| P^t(x,y)/\pi(y) - 1 \bigr| \le \lambda_\ast^t / \sqrt{\pi(x)\pi(y)}$;
3. $\|P^t(x,\cdot) - \pi\|_{TV} \le \tfrac12\sqrt{(1-\pi(x))/\pi(x)}\;\lambda_\ast^t$, hence $d(t) \le \tfrac12 \sqrt{(1-\pi_{\min})/\pi_{\min}}\;\lambda_\ast^t$.

## Proof sketch

The density $\nu P^t/\pi$ minus $1$ is obtained by applying the self-adjoint operator $P^t$ (in $\ell^2(\pi)$) to the mean-zero function $\nu/\pi - 1$, whose norm contracts by $\lambda_\ast^t$. The pointwise bound is Cauchy-Schwarz on the spectral decomposition, and total variation is at most half the square root of $\chi^2$.

## Depends on

- [Absolute spectral gap and l2 contraction factor of a reversible chain](absolute-spectral-gap.md)
- [Distance to stationarity and total-variation mixing time](../coupling-and-total-variation-mixing/distance-to-stationarity-and-mixing-time.md)

## Proof depends on

- [Absolute spectral gap and l2 contraction factor of a reversible chain](absolute-spectral-gap.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017.
