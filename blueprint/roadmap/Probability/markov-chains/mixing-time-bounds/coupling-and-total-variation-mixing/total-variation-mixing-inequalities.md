# Basic inequalities for total-variation mixing

Let $P$ be a Markov kernel on a finite set with stationary distribution $\pi$, and let $d, \bar d, t_{\mathrm{mix}}$ be as defined for $(P, \pi)$. Then for all $s, t, \ell \in \mathbb{N}$:

1. $d(t) \le \bar d(t) \le 2\,d(t)$;
2. $\bar d(s+t) \le \bar d(s)\,\bar d(t)$, and both $d$ and $\bar d$ are non-increasing;
3. $d(\ell t) \le (2 d(t))^\ell$;
4. $t_{\mathrm{mix}}(\varepsilon) \le t$ if and only if $d(t) \le \varepsilon$, and $t_{\mathrm{mix}}(\varepsilon) \le \lceil \log_2 \varepsilon^{-1} \rceil\, t_{\mathrm{mix}}(1/4)$ for $0 < \varepsilon \le 1$.

## Proof sketch

Stationarity writes $\pi$ as a mixture of the rows $P^t(y,\cdot)$, giving $d \le \bar d$; the triangle inequality gives $\bar d \le 2d$. Submultiplicativity follows by running a common kernel from an optimal coupling of two rows: the second stage can separate only when the first did. Items 3 and 4 iterate submultiplicativity with $d(t_{\mathrm{mix}}(1/4)) \le 1/4$.

## Depends on

- [Distance to stationarity and total-variation mixing time](distance-to-stationarity-and-mixing-time.md)

## Proof depends on

- [Coupling of two probability measures](../../../../MeasureTheory/optimal-transport/kantorovich-duality/is-coupling.md)
- [The distance to stationarity does not increase](../../mixing-times-of-markov-chains/tv-dist-pow-succ-le.md)

## Sources

- David A. Levin and Yuval Peres, "Markov Chains and Mixing Times", 2nd ed., American Mathematical Society, 2017.
