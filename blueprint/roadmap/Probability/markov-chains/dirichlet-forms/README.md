# Dirichlet forms

A Dirichlet form is a closed symmetric form on $L^2(X; m)$ on which the unit contraction
$u \mapsto (0 \vee u) \wedge 1$ operates. By the Beurling–Deny theorem these are exactly the forms
of symmetric Markovian semigroups, and by Fukushima's theorem a regular Dirichlet form is the form of
an $m$-symmetric Hunt process; Albeverio, Ma and Röckner extended this to quasi-regular forms on
general (possibly infinite-dimensional) state spaces and showed that quasi-regularity is exactly the
condition for a nice associated process (Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric
Markov Processes*, 2nd ed., 2011; Ma and Röckner, *Introduction to the Theory of (Non-Symmetric)
Dirichlet Forms*, 1992).

On a finite set everything is explicit: the form of a reversible sub-Markovian generator $Q$ is
$\mathcal E(f, f) = \tfrac12 \sum_{x,y} m(x) Q(x,y) (f(x) - f(y))^2 + \sum_x m(x) k(x) f(x)^2$ with
killing rate $k = -\sum_y Q(\cdot, y)$, it has the Markov property, and conversely a symmetric form
on $\mathbb R^n$ is unit-contractive exactly when it is of this kind. The spectral gap and the
log-Sobolev constant of a finite chain are the best constants (when the optimisation domains are nonempty) in $\lambda \operatorname{Var}(f) \le
\mathcal E(f, f)$ and $\alpha \mathcal L(f) \le \mathcal E(f, f)$.

## Finite state spaces

- [Dirichlet form of a sub-Markovian generator on a finite set](form.md)
- [The form is symmetric](form-comm.md)
- [Killing rate of a generator](killing-rate.md)
- [The form of a reversible generator is $-\langle f, Qg \rangle_m$](form-eq-neg-sum-mul-mul-vec.md)
- [No killing for a Markov kernel](killing-rate-sub-one.md)
- [The Dirichlet form of a Markov kernel](form-sub-one.md)
- [Sinclair's identity in Dirichlet-form terms](form-sub-one-self-eq-sum-mul-sub-mul-vec.md)
- [The Dirichlet form of a Markov kernel is nonnegative](form-sub-one-self-nonneg.md)
- [Unit contraction](unit-contraction.md)
- [The unit contraction is a normal contraction (differences)](abs-unit-contraction-sub-le.md)
- [The unit contraction is a normal contraction (values)](abs-unit-contraction-le.md)
- [Energy comparison under a normal contraction](form-le-form-of-normal-contraction.md)
- [The Markov property of the form of a sub-Markovian generator](form-unit-contraction-le.md)
- [The form of a sub-Markovian generator is nonnegative](form-self-nonneg.md)
- [Bilinear form of a matrix on $\mathbb{R}^S$](matrix-form.md)
- [A symmetric matrix form is the form of the generator $-A$](matrix-form-eq-form.md)
- [Beurling–Deny criterion on $\mathbb{R}^n$](unit-contraction-le-iff.md)
- [Beurling–Deny on $\mathbb{R}^n$: unit-contractive forms come from sub-Markovian generators](unit-contraction-le-iff-exists-generator.md)

## Spectral gap and log-Sobolev constant

- [Variance of a function under a weight vector](weighted-variance.md)
- [The variance is nonnegative](weighted-variance-nonneg.md)
- [Spectral gap of a finite Markov kernel, in Dirichlet-form terms](spectral-gap.md)
- [The spectral gap is nonnegative](spectral-gap-nonneg.md)
- [Poincaré inequality with the spectral gap](spectral-gap-mul-weighted-variance-le.md)
- [Poincaré constants bound the spectral gap from below](le-spectral-gap.md)
- [Sinclair's Poincaré hypothesis is a lower bound on the spectral gap](inv-le-spectral-gap-iff-poincare.md)
- [Mixing of a lazy reversible chain from its spectral gap](is-mixed-at-of-le-spectral-gap.md)
- [Entropy-like functional of the log-Sobolev inequality](entropy-functional.md)
- [The entropy-like functional is nonnegative](entropy-functional-nonneg.md)
- [Log-Sobolev constant of a finite Markov kernel](log-sobolev-constant.md)
- [The log-Sobolev constant is nonnegative](log-sobolev-constant-nonneg.md)
- [Log-Sobolev inequality with the log-Sobolev constant](log-sobolev-constant-mul-entropy-functio.md)
- [The log-Sobolev constant is at most half the spectral gap](two-mul-log-sobolev-constant-le-spectral.md)
- [Expansion of the entropy functional near the constant $1$](entropy-functional-one-add-mul-ge.md)
- [Second-order expansion of $t \log t$ at $1$](abs-mul-log-one-add-sub-le.md)

## Forms on $L^2(X; m)$

- [Symmetric form on $L^2(X; m)$](symmetric-form.md)
- [The form $\mathcal E_1$](energy-one.md)
- [$\mathcal E_1$ dominates the squared norm](norm-sq-le-energy-one.md)
- [$\mathcal E_1$ dominates $\mathcal E$](form-le-energy-one.md)
- [Closed symmetric form](is-closed.md)
- [Closable symmetric form](is-closable.md)
- [A form with a closed extension is closable](is-closable-of-le.md)
- [Closed forms are closable](is-closable-of-is-closed.md)
- [The unit clamp is $1$-Lipschitz](lipschitz-with-unit-clamp.md)
- [Unit contraction on $L^2$](unit-contraction-lp.md)
- [The unit contraction on $L^2$ is pointwise](unit-contraction-lp-ae-eq.md)
- [The unit contraction does not increase the $L^2$ norm](norm-unit-contraction-lp-le.md)
- [The unit contraction operates on a form](unit-contraction-operates.md)
- [Dirichlet form](is-dirichlet-form.md)
- [Beurling–Deny: the unit contraction operates on a closed form iff its resolvent is Markovian](unit-contraction-operates-iff-resolvent.md)
- [The Dirichlet form of linear Brownian motion is $\frac{1}{2} \int f'^2$](tendsto-brownian-approximating-form.md)

## Regularity, quasi-regularity and associated processes

Regularity and quasi-regularity are the topological conditions under which a Markov process is
associated with a Dirichlet form: a regular Dirichlet form is the form of a Hunt process
(Fukushima), and quasi-regularity characterises the Dirichlet forms associated with nice right
processes (Albeverio, Ma and Röckner). Nests, exceptional sets and quasi-continuity are the notions
in which quasi-regularity is phrased.

- [Regular symmetric form](is-regular.md)
- [Elements of the domain vanishing outside a set](vanishing-outside.md)
- [Nests of a symmetric form](is-nest.md)
- [Exceptional sets of a symmetric form](is-exceptional.md)
- [Quasi-continuous functions](is-quasi-continuous.md)
- [The whole space is a nest](is-nest-const-univ.md)
- [The empty set is exceptional](is-exceptional-empty.md)
- [Continuous functions are quasi-continuous](is-quasi-continuous-of-continuous.md)
- [Quasi-regular symmetric form](is-quasi-regular.md)
- [Regular forms are quasi-regular](is-quasi-regular-of-is-regular.md)

## Related topics

- [Mixing times of Markov chains](../mixing-times-of-markov-chains/README.md): Sinclair's identity for the
  Dirichlet form of a reversible matrix and his route from a Poincaré inequality to mixing, expressed in
  terms of the spectral gap.
- [Canonical paths and multicommodity flow](../canonical-paths-and-multicommodity-flow/README.md): geometric
  lower bounds on the spectral gap, i.e. Poincaré inequalities for the Dirichlet form.
- [Finite continuous-time Markov chains](../finite-continuous-time-markov-chains/README.md): rate matrices
  (conservative sub-Markovian generators), detailed balance and the semigroup $e^{tQ}$ whose form is studied here.
- [Markov processes from transition semigroups](../markov-processes-from-transition-semigroups/README.md):
  processes built from semigroups by projective limits, the measure-theoretic side of the form–process
  correspondence.
- [Construction and sample paths of Brownian motion](../../stochastic-calculus/construction-and-sample-paths-of-brownian-motion/README.md):
  Brownian motion, whose Dirichlet form is $\tfrac12 \int |\nabla f|^2$.
- [Random walks on finite groups](../../random-walks/random-walks-on-finite-groups/README.md): Diaconis's
  random walks, a main source of finite reversible chains with computable spectral gaps.
- [Transport-cost inequalities](../../concentration-inequalities/transport-cost-inequalities/README.md):
  log-Sobolev inequalities on metric measure spaces and the Otto–Villani theorem.
- [Potential theory](../../../Analysis/potential-theory/README.md): Dirichlet forms were introduced by
  Beurling and Deny as an axiomatic potential theory; nests, exceptional sets and quasi-continuity
  extend the classical notions.
- [Effective resistance and electrical networks](../../../GraphTheory/algebraic-graph-theory/part-01/effective-resistance-and-electrical-networks/README.md): for a reversible chain with conductances $\pi(x) P(x, y)$, the Dirichlet form is the network energy, whose minimum over potentials equal to $0$ and $1$ at two states is their effective conductance (Dirichlet's principle).
