# Structure theorems for Boolean functions

Theorems saying that a Boolean function $f : \{-1, 1\}^n \to \{-1, 1\}$ with a simple Fourier spectrum or few influential coordinates is close to a simple function: Friedgut–Kalai–Naor (degree-1 concentration forces a dictator), Friedgut's junta theorem (small total influence forces a junta), the Level-1 Inequality and Majority Is Stablest.

- [Friedgut–Kalai–Naor (FKN) Theorem](fkn-theorem.md)
- [Friedgut's Junta Theorem](friedgut-junta-theorem.md)
- [Level-1 Inequality](level-one-inequality.md)
- [Majority Is Stablest](majority-is-stablest.md)
- [Noise stability of a coordinate Laplacian](bool-noise-stab-derivative-le.md)
- [Few coordinates have large influence](card-influential-le.md)
- [Friedgut's junta theorem, explicit form](exists-junta-bool-dist-le.md)
- [Spectral part of Friedgut's argument](sum-sq-not-subset-le-of-influence.md)
- [Level-k Inequalities](level-k-inequality.md)
- [Fourier expansion of the coordinate derivative](bool-fourier-coeff-coord-derivative.md)
- [Corollary 9.12: stable influences of Boolean functions](stable-influence-third-le.md)

## Related topics

- [Influences and the noise operator on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/README.md): the influences, total influence and noise stability in these statements.
- [Bonami–Beckner hypercontractivity](../../../Probability/concentration-inequalities/bonami-beckner-hypercontractivity/README.md): the main tool in the proofs of FKN and Friedgut's theorem.
- [Kahn–Kalai–Linial inequality](../kahn-kalai-linial-inequality/README.md): the companion theorem: every Boolean function has a coordinate of influence $\Omega(\mathrm{Var}[f] \log n / n)$.
- [Majority is least stable conjecture](../majority-is-least-stable-conjecture/README.md): the opposite question: whether majority minimizes noise stability among linear threshold functions.
- [Junta approximation of monotone Boolean functions](../junta-approximation-of-monotone-boolean-function/README.md): a junta approximation problem for monotone functions, in the spirit of Friedgut's theorem.
- [Inapproximability of MAX-CUT](../../../TheoryOfComputation/pcp-and-inapproximability/inapproximability-of-max-cut/README.md): Majority Is Stablest gives Unique-Games hardness of Max-Cut at the Goemans–Williamson ratio.
- [Arrow's impossibility theorem](../../../GameTheory/social-choice/arrow-s-impossibility-theorem/README.md): Kalai's Fourier-analytic proof of Arrow's theorem; its robust version (O'Donnell, Corollary 2.60) follows from the FKN Theorem.
