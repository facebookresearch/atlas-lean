# Ben Arous–Guionnet large deviation principle

For $\beta > 0$, the laws of the [empirical spectral measure](spectral-empirical-measure.md) $L_N$
under the [Gaussian β-ensemble](beta-ensemble.md) satisfy, in the space of probability measures on
$\mathbb{R}$ with the weak topology, a
[large deviation principle at speed](../large-deviation-principle/satisfies-ldpat-speed.md) $N^2$
with the [rate function](ben-arous-guionnet-rate.md) $I_\beta$, and $I_\beta$ is a good rate
function (its sublevel sets are compact).

Proof in the sources: goodness of $I_\beta$ is proved first (Anderson, Guionnet and Zeitouni, Lemma
2.6.2(c)). Then write the density of $Q^N_\beta$ as
$\exp\bigl(-\frac{\beta}{2} N^2 \iint_{x \ne y} f \, dL_N\, dL_N\bigr) \prod_i e^{-\beta\lambda_i^2/4}$;
the upper bound truncates the singular kernel $f$ and uses lower semicontinuity of the energy, the
lower bound moves the eigenvalues to a discretisation of the target measure, and the normalising
constant is identified from the two bounds. As for Sanov's theorem, the statement assumes that the
open sets of the weak topology are measurable for the σ-algebra on probability measures generated
by the evaluations $\mu \mapsto \mu(B)$; this holds on $\mathbb{R}$.

## Background

- [The Ben Arous–Guionnet rate function](ben-arous-guionnet-rate.md): the definition of $I_\beta$, whose
  goodness the proof establishes first.
- [The semicircle law is the unique zero of the rate function](ben-arous-guionnet-rate-eq-zero-iff.md):
  with it, the principle gives the almost sure convergence of $L_N$ to the semicircle law.
- [Sanov's theorem](../sanov-s-theorem/README.md): the large deviation principle at speed $N$ for
  empirical measures of independent samples, whose rate is relative entropy instead of free entropy.

## Sources

- A. Guionnet, "Large deviations and stochastic calculus for large random matrices", *Probability
  Surveys* 1 (2004), 72–172, arXiv:math/0409277, Theorem 3.1 (for $\beta = 1, 2, 4$).
- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), Theorem 2.6.1 (for every $\beta > 0$ and potentials $V$; here
  $V(x) = \beta x^2/4$), and Lemma 2.6.2(c) for the goodness of the rate function.
- G. Ben Arous and A. Guionnet, "Large deviations for Wigner's law and Voiculescu's non-commutative
  entropy", *Probab. Theory Related Fields* 108 (1997), 517–542 (cited by both as the original).
