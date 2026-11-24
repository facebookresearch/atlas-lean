# Relative entropy between Bernoulli laws

For $p \in [0, 1]$ let $\mathcal B(p) = (1 - p)\,\delta_0 + p\,\delta_1$ be the Bernoulli law of parameter $p$, a
probability measure on $\mathbb R$ with its Borel σ-algebra. For all $p, q \in [0, 1]$,

$$
D\big(\mathcal B(p) \,\|\, \mathcal B(q)\big) = d(p, q),
$$

where $D \in [0, \infty]$ is the relative entropy of measures and $d \in (-\infty, \infty]$ the binary relative
entropy; the equality holds in $(-\infty, \infty]$, so in particular $d(p, q) \ge 0$. Also the divergence is
infinite exactly when $q \in \{0, 1\}$ and $p \ne q$, that is, when $\mathcal B(p)$ is not absolutely continuous
with respect to $\mathcal B(q)$. The same holds for the laws $(1 - p)\,\delta_y + p\,\delta_x$ and
$(1 - q)\,\delta_y + q\,\delta_x$ on any measurable space with measurable singletons, for points $x \ne y$.

## Depends on

- [Relative entropy of measures](kl-div.md)
- [Binary relative entropy](binary-relative-entropy.md)
- [Probability measure](../../../Probability/foundations/probability-measures/is-probability-measure.md)
- [Borel σ-algebra](../../../MeasureTheory/measurable-spaces/measurable-spaces-and-measurable-functions/sigma-algebras/borel.md)
- [σ-algebra](../../../MeasureTheory/measurable-spaces/measurable-spaces-and-measurable-functions/sigma-algebras/measurable-space.md)

## Informally uses

- [Kullback–Leibler divergence of finite probability laws](to-real-kl-div-to-measure.md): the finite sum that the
  divergence reduces to for laws with finite support.

## Sources

- T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020 (author copy,
  <https://tor-lattimore.com/downloads/book/book.pdf>), Section 14.2: Theorem 14.1 and the formula for
  $D(\mathcal B(p), \mathcal B(q))$ that follows it, identified there with $d(p, q)$ of Definition 10.1.
- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025
  (prepublication version of 16 August 2024, with the published numbering), Example 2.1, eq. (2.6).
