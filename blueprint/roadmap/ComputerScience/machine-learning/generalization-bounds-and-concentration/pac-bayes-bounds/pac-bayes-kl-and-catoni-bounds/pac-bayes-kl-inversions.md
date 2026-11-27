# Explicit inversions of the PAC-Bayes-kl bound

In the setting of the PAC-Bayes-kl bound, let $q = \mathbb{E}_Q L_S$ and let $c$ be either (a) $c = (\mathrm{KL}(Q\,\|\,P) + \ln((m+1)/\delta))/m$ for a binary loss and any $m \ge 1$, or (b) $c = (\mathrm{KL}(Q\,\|\,P) + \ln(2\sqrt m/\delta))/m$ for a loss with values in $[0,1]$ and $m \ge 8$. With probability at least $1-\delta$, every posterior $Q$ with $\mathrm{KL}(Q\,\|\,P) < \infty$ satisfies each of:

1. (Pinsker form) $\mathbb{E}_Q L_D \le q + \sqrt{c/2}$, that is, the McAllester-type bound with denominator $2m$;
2. (sharp fast rate) $\mathbb{E}_Q L_D \le q + c + \sqrt{c^2 + 2qc}$;
3. (relaxed fast rate) $\mathbb{E}_Q L_D \le q + \sqrt{2qc} + 2c$;
4. (realizable case) if $q = 0$, then $\mathbb{E}_Q L_D \le 1 - e^{-c} \le c$.

## Proof sketch

Each case gives $\mathrm{kl}(q\,\|\,\mathbb{E}_Q L_D) \le c$: case (a) is the PAC-Bayes-kl bound, case (b) is Theorem 1 of Tolstikhin and Seldin, which requires $m \ge 8$. Binary Pinsker $\mathrm{kl}(q\|p) \ge 2(p-q)^2$ gives item 1. For $p \ge q$, the lower bound $\mathrm{kl}(q\|p) \ge (p-q)^2/(2p)$ turns $\mathrm{kl} \le c$ into a quadratic inequality in $p$ whose larger root is $q + c + \sqrt{c^2+2qc}$; item 3 follows from $\sqrt{a+b} \le \sqrt a + \sqrt b$. At $q = 0$, $\mathrm{kl}(0\|p) = -\ln(1-p)$.

## Depends on

- [Seeger's PAC-Bayes-kl bound for binary losses](pac-bayes-kl-bound.md)
- [Binary Pinsker inequality on the closed interval](../../../../../InformationTheory/information-inequalities/binary-pinsker-of-mem-icc.md)

## Proof depends on

- [Binary Pinsker inequality on the closed interval](../../../../../InformationTheory/information-inequalities/binary-pinsker-of-mem-icc.md)
- [Lower bounds and inversions of the binary relative entropy](../../../../../InformationTheory/information-inequalities/binary-relative-entropy/binary-kl-lower-bounds-and-inversions.md)

## Sources

- M. Seeger, "PAC-Bayesian Generalisation Error Bounds for Gaussian Process Classification", Journal of Machine Learning Research 3, 2002, Theorem 1.
- I. O. Tolstikhin and Y. Seldin, "PAC-Bayes-Empirical-Bernstein Inequality", Advances in Neural Information Processing Systems 26, 2013, Theorem 1.
