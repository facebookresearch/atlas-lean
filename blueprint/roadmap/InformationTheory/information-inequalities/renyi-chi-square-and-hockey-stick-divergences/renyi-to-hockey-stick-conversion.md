# Conversion from Renyi divergence to hockey-stick divergence

Let $p, q$ be discrete probability distributions on a countable set, $\alpha > 1$, $\varepsilon \ge 0$ and $\delta > 0$. If $D_\alpha(p\|q) \le \varepsilon$ (natural logarithm), then

$$
E_{c}(p \,\|\, q) \le \delta \qquad \text{for } c = \exp\Big(\varepsilon + \frac{\ln(1/\delta)}{\alpha - 1}\Big).
$$

Consequently an $(\alpha, \varepsilon)$-Renyi differentially private mechanism is $(\varepsilon + \frac{\ln(1/\delta)}{\alpha-1}, \delta)$-differentially private for every $\delta \in (0,1)$. More generally, for all $t \ge 0$ and $\varepsilon'$, $\sum_x (p(x) - e^{\varepsilon'} q(x))_+ \le e^{-t\varepsilon'} \sum_x p(x)(p(x)/q(x))^{t}$.

## Proof sketch

On the excess set, $p(x) - e^{\varepsilon'} q(x) \le p(x) \le p(x)(p(x)/(e^{\varepsilon'}q(x)))^t$, a Markov-type bound; summing gives the general inequality. Take $t = \alpha - 1$, so the right side is $e^{-(\alpha-1)\varepsilon'} M_\alpha(p\|q) \le e^{(\alpha-1)(\varepsilon - \varepsilon')}$, and choose $\varepsilon'$ to make this $\delta$.

## Depends on

- [Renyi divergence of discrete distributions](renyi-divergence.md)
- [Hockey-stick divergence](hockey-stick-divergence.md)

## Proof depends on

- [Nonnegativity, data processing and adaptive composition of Renyi divergence](renyi-divergence-properties.md)

## Sources

- I. Mironov, "Renyi Differential Privacy", IEEE 30th Computer Security Foundations Symposium (CSF), 2017.
