# Explicit inversions of the PAC-Bayes-kl bound

In the setting of the PAC-Bayes-kl bound, let $c = (\mathrm{KL}(Q\,\|\,P) + \ln((m+1)/\delta))/m$ and $q = \mathbb{E}_Q L_S$. With probability at least $1-\delta$, every posterior $Q$ with $\mathrm{KL}(Q\,\|\,P) < \infty$ satisfies each of:

1. (Pinsker form) $\mathbb{E}_Q L_D \le q + \sqrt{c/2}$, that is, the McAllester-type bound with denominator $2m$;
2. (sharp fast rate) $\mathbb{E}_Q L_D \le q + c + \sqrt{c^2 + 2qc}$;
3. (relaxed fast rate) $\mathbb{E}_Q L_D \le q + \sqrt{2qc} + 2c$;
4. (realizable case) if $q = 0$, then $\mathbb{E}_Q L_D \le 1 - e^{-c} \le c$.

## Proof sketch

Binary Pinsker $\mathrm{kl}(q\|p) \ge 2(p-q)^2$ gives item 1. For $p \ge q$, the lower bound $\mathrm{kl}(q\|p) \ge (p-q)^2/(2p)$ turns $\mathrm{kl} \le c$ into a quadratic inequality in $p$ whose larger root is $q + c + \sqrt{c^2+2qc}$; item 3 follows from $\sqrt{a+b} \le \sqrt a + \sqrt b$. At $q = 0$, $\mathrm{kl}(0\|p) = -\ln(1-p)$.

## Depends on

- [The PAC-Bayes-kl bound of Seeger and Maurer](pac-bayes-kl-bound.md)
- [Binary Pinsker inequality on the closed interval](../../../../InformationTheory/information-inequalities/binary-pinsker-of-mem-icc.md)

## Proof depends on

- [Binary Pinsker inequality on the closed interval](../../../../InformationTheory/information-inequalities/binary-pinsker-of-mem-icc.md)
- [Lower bounds and inversions of the binary relative entropy](../../../../InformationTheory/information-inequalities/binary-relative-entropy/binary-kl-lower-bounds-and-inversions.md)

## Sources

- M. Seeger, "PAC-Bayesian Generalisation Error Bounds for Gaussian Process Classification", Journal of Machine Learning Research, 2002.
- A. Maurer, "A Note on the PAC Bayesian Theorem", arXiv preprint cs/0411099, 2004.
- I. O. Tolstikhin and Y. Seldin, "PAC-Bayes-Empirical-Bernstein Inequality", Advances in Neural Information Processing Systems, 2013.
