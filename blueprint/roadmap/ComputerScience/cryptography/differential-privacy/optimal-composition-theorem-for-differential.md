# Optimal composition theorem for differential privacy

For every $\varepsilon \ge 0$, $\delta \in [0,1]$ and $k \ge 1$, the class of $(\varepsilon, \delta)$-differentially private mechanisms satisfies, under $k$-fold adaptive composition, $\bigl((k - 2i)\varepsilon,\ 1 - (1 - \delta)^k (1 - \delta_i)\bigr)$-differential privacy for every $i \in \{0, 1, \dots, \lfloor k/2 \rfloor\}$, where

$$\delta_i = \frac{\sum_{\ell = 0}^{i-1} \binom{k}{\ell} \bigl(e^{(k-\ell)\varepsilon} - e^{(k - 2i + \ell)\varepsilon}\bigr)}{(1 + e^{\varepsilon})^k}.$$

Hence the privacy region of $k$-fold composition lies in the intersection of the regions $R((k - 2i)\varepsilon, 1 - (1 - \delta)^k (1 - \delta_i))$. This is tight: the $k$-fold composition of an explicit mechanism attains exactly this region, so no better guarantee holds for the whole class.

## Proof depends on

- [Basic composition](differentially-private-pi.md)
- [Differential privacy as hypothesis testing](differential-privacy-as-hypothesis-testing.md)

## Sources

- P. Kairouz, S. Oh and P. Viswanath, "The composition theorem for differential privacy", *IEEE Transactions on Information Theory* 63(6):4037–4049, 2017, <https://kairouzp.github.io/p4_composition_theorem.pdf>, Section III, Theorem III.3, and Section IV.A (achievability)
