# Simple Lebesgue spectrum on the smooth three-torus

On $M=(\mathbb R/\mathbb Z)^3$, let $m$ be the product of the normalized Haar probabilities. Write $H_0=\{g\in L^2(M,m;\mathbb C):\int g\,dm=0\}$. There is a bijection $T:M\to M$ preserving $m$ such that $T$ and $T^{-1}$ each have smooth local lifts through $\mathbb R^3\to M$ at every point of the cover. The map $T$ is ergodic.

There is an $f\in H_0$ that is real almost everywhere, and its integer Koopman iterates $v_n=f\circ T^n$, interpreted as almost-everywhere equalities for each $n\in\mathbb Z$, form an orthonormal family with dense **complex** linear span in all of $H_0$. For the circle with normalized Haar measure there is a surjective complex linear isometry $W:H_0\to L^2(\mathbb R/\mathbb Z;\mathbb C)$ satisfying

$$ W(g\circ T)(z)=e^{2\pi i z}(Wg)(z) \quad\text{a.e. in }z,\qquad g\in H_0. $$

Here $g\circ T$ is the mean-zero $L^2$ class given by almost-everywhere composition with $T$.

## Expansion

1. Identify smooth local lifts with the smooth torus model and prove that measure-preserving composition and its inverse act on the complex integral kernel, independently of representatives. The [real $L^2$ Koopman composition lemma](von-neumann-mean-ergodic-theorem/koopman-apply-ae-eq.md) is a comparison; it does not supply the complex mean-zero representation.
2. Construct the smooth measure-preserving map and a real unit vector, and prove completeness of its bilateral orbit, not only orthogonality. Derive ergodicity by ruling out nonzero invariant mean-zero vectors.
3. Use the unit-circle Fourier basis to extend $v_n\mapsto e^{2\pi i n z}$ to the full isometry and check the sign of the multiplier.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ThreeTorus.lean#L21-L83) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/144.md).
- OpenAI, [A smooth three-torus diffeomorphism with simple Lebesgue spectrum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-smooth-three-torus-diffeomorphism-with-simple-Lebesgue-spectrum-September-23-2026/paper.pdf) (September 23, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
