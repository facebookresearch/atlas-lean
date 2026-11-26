# Moment comparisons and tail bounds for low-degree functions

For $f : \{-1,1\}^n \to \mathbb{R}$ of degree at most $k$: (1) for $0 < p \le 2$, $\|f\|_2 \le e^{k(2/p - 1)}\|f\|_p$, in particular $\|f\|_2 \le e^k \|f\|_1$; (2) the tail bound $\Pr[|f| \ge t\|f\|_2] \le \exp\big(-\frac{k}{2e} t^{2/k}\big)$ for $t \ge (2e)^{k/2}$.

## Proof sketch

(1) Interpolate between $p$ and a large $q$ using Hölder and the Bonami bound $\|f\|_q \le \sqrt{q-1}^{\,k}\|f\|_2$, optimizing $q$. (2) Markov's inequality on $|f|^q$ with $q$ chosen as a function of $t$.

## Depends on

- [Boolean degree](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/fourier-analysis-on-the-boolean-cube/boolean-degree.md)

## Proof depends on

- [Bonami Lemma](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/bonami-lemma.md)
- [L^p norms under a uniform distribution increase with p](../fourier-expansion-supplements/lp-norms-increase-with-p.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
