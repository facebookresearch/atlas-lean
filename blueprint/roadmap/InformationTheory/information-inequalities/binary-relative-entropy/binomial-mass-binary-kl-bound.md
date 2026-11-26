# Binomial probabilities are bounded by the exponential of binary relative entropy

For every $p \in [0,1]$ and integers $0 \le k \le m$ with $m \ge 1$,

$$
\binom{m}{k} p^k (1-p)^{m-k} \le \exp\Big(-m\, \mathrm{kl}\Big(\frac{k}{m} \,\Big\|\, p\Big)\Big),
$$

where $\mathrm{kl}$ is the binary relative entropy in nats.

## Proof sketch

Multiplying both sides by $\exp(m\,\mathrm{kl}(k/m\|p))$ turns the left side into $\binom{m}{k} q^k (1-q)^{m-k}$ with $q = k/m$, which is the probability of exactly $k$ successes in $m$ Bernoulli($q$) trials and hence at most $1$.

## Depends on

- [Binary relative entropy](binary-relative-entropy.md)

## Sources

- T. M. Cover and J. A. Thomas, "Elements of Information Theory", Wiley-Interscience, 2nd ed., 2006.
