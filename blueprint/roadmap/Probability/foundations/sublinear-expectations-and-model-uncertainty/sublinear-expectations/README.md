# Sublinear expectations

Let $\mathcal{H}$ be a linear space of real functions on a set $\Omega$. A functional $\mathbb{E}$ on real functions on $\Omega$ is a sublinear expectation on $\mathcal{H}$ if $\mathcal{H}$ contains the constants and, for all $X, Y \in \mathcal{H}$: $\mathbb{E}[Y] \le \mathbb{E}[X]$ whenever $Y \le X$ (monotonicity); $\mathbb{E}[c] = c$ for every constant $c$ (constant preservation); $\mathbb{E}[X + Y] \le \mathbb{E}[X] + \mathbb{E}[Y]$ (subadditivity); and $\mathbb{E}[cX] = c \, \mathbb{E}[X]$ for $c \ge 0$ (positive homogeneity). Only the values of $\mathbb{E}$ on $\mathcal{H}$ are constrained, and, unlike Peng's definition, $\mathcal{H}$ need not contain $|X|$ for each of its elements.

## Idea

Sublinear expectations model uncertainty about the probability law itself. If the law is only known to lie in a family $\{P_\theta\}$, a cautious evaluation of an uncertain quantity $X$ is the upper expectation $\sup_\theta \mathbb{E}_{P_\theta}[X]$, and this functional is sublinear. The representation theorem gives the converse: every sublinear expectation is a maximum of linear expectations, $\mathbb{E}[X] = \max_\theta \mathbb{E}_\theta[X]$ over the monotone, constant-preserving linear functionals dominated by $\mathbb{E}$. The proof applies the Hahn–Banach theorem to the sublinear functional $\mathbb{E}$, and the linear expectations it produces are in general only finitely additive. On a finite set $\Omega$ they are probability vectors; for instance $\mathbb{E}[X] = \max_\omega X(\omega)$, the worst case, is the maximum over all probability vectors.

## Statements

- [Sublinear expectation](is-sublinear-expectation.md)
- [Representation of a sublinear expectation as a maximum of linear expectations](is-greatest.md): representation as a maximum of linear expectations
- [Representation on a finite scenario set](is-greatest-finite.md): finite scenario case
- [Representation of a sublinear expectation, pointwise form](exists-linear-expectation.md): representation theorem, pointwise form
- [Representation of a sublinear functional as a maximum of linear functionals](is-greatest-linear-le.md): functional-analytic form
- [Representation of a sublinear functional, pointwise form](exists-linear-le-eq.md): lemma: representation of a sublinear functional, used for the representation theorem
- [Positively homogeneous functionals vanish at zero](map-zero-of-pos-hom.md): lemma used in the proof of the representation theorem

## Sources

- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*, arXiv:1002.4546, 2010.
