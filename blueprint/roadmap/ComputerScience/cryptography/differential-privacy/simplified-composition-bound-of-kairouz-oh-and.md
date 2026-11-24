# Simplified composition bound of Kairouz, Oh and Viswanath

For every $\varepsilon > 0$, $\delta \in [0,1]$ and $\tilde\delta \in (0,1]$, the class of $(\varepsilon, \delta)$-differentially private mechanisms satisfies $\bigl(\tilde\varepsilon,\ 1 - (1 - \delta)^k (1 - \tilde\delta)\bigr)$-differential privacy under $k$-fold adaptive composition, where

$$\tilde\varepsilon = \min\Bigl\{ k\varepsilon,\ \frac{(e^\varepsilon - 1)\varepsilon k}{e^\varepsilon + 1} + \varepsilon\sqrt{2k \log\bigl(e + \sqrt{k\varepsilon^2}/\tilde\delta\bigr)},\ \frac{(e^\varepsilon - 1)\varepsilon k}{e^\varepsilon + 1} + \varepsilon\sqrt{2k\log(1/\tilde\delta)} \Bigr\}.$$

This region contains the one given by the advanced composition theorem of Dwork, Rothblum and Vadhan.

## Proof depends on

- [Optimal composition theorem for differential privacy](optimal-composition-theorem-for-differential.md)
- [Advanced composition](differentially-private-pi-advanced.md)

## Sources

- P. Kairouz, S. Oh and P. Viswanath, "The composition theorem for differential privacy", *IEEE Transactions on Information Theory* 63(6):4037–4049, 2017, Theorem III.4; <https://kairouzp.github.io/p4_composition_theorem.pdf>
