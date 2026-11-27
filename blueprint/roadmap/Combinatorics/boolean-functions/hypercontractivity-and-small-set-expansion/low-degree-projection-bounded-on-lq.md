# The low-degree projection is bounded on L^q

For every real $f$ on $\{-1,1\}^n$ and $k \ge 0$: $\|f^{\le k}\|_q \le \sqrt{q - 1}^{\,k}\|f\|_q$ for $q \ge 2$, and $\|f^{\le k}\|_q \le (1/\sqrt{q-1})^{k}\|f\|_q$ for $1 < q \le 2$. Moreover for $0 < \rho \le 1$ and $q \ge 2$, $\|f^{\le k}\|_q \le (\sqrt{q-1}/\rho)^k\, \|T_\rho f\|_q$.

## Proof sketch

For $q \ge 2$: $\|f^{\le k}\|_q \le \sqrt{q-1}^{\,k}\|f^{\le k}\|_2 \le \sqrt{q-1}^{\,k}\|f\|_2 \le \sqrt{q-1}^{\,k}\|f\|_q$ by hypercontractivity and orthogonality. For $q \le 2$ use duality with the conjugate exponent. For the noise version, $f^{\le k} = T_{1/\rho}^{\le k} T_\rho f$ and $T_{1/\rho}$ amplifies degree-$j$ parts by $\rho^{-j}$.

## Depends on

- [Fourier weight at each degree](../fourier-expansion-supplements/fourier-weight-at-each-degree.md)
- [Noise operator on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-op.md)

## Proof depends on

- [Bonami Lemma](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/bonami-lemma.md)
- [Hypercontractivity Theorem (Bonami–Beckner)](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/hypercontractivity-theorem.md)
- [L^p seminorms under a probability measure increase with the exponent](../fourier-expansion-supplements/lp-norms-increase-with-p.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
