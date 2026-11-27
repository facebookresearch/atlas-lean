# Friedgut–Kalai–Naor (FKN) Theorem

There is a universal constant $C$ such that for every $n \ge 1$: if
$f : \{-1, 1\}^n \to \{-1, 1\}$ has degree-1 Fourier weight
$\mathbf{W}^1[f] = \sum_{|S| = 1} \hat f(S)^2 \ge 1 - \delta$, then $f$ is $C\delta$-close to a
dictator $\chi_i$ or a negated dictator $-\chi_i$ for some coordinate $i$.

The source writes the closeness as $O(\delta)$; Theorem 5.33 in Section 5.4 of the same source
improves it to $\delta/4 + O(\delta^2 \log(2/\delta))$. The hypothesis $n \ge 1$ is implicit in the source.

## Sources

- E. Friedgut, G. Kalai and A. Naor, "Boolean functions whose Fourier transform is concentrated on
  the first two levels", *Adv. in Appl. Math.* 29 (2002), 427–437.
- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), FKN Theorem, stated in Section 2.5, proved in Section 9.1; the sharper closeness is Theorem 5.33 (Section 5.4).

## Informally uses

- [Bonami Lemma](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/bonami-lemma.md):
  the proof in Section 9.1 applies Theorem 9.7, an anticoncentration bound for low-degree
  polynomials derived from the Bonami Lemma, to $\ell^2$ where $\ell = f^{=1}$.
