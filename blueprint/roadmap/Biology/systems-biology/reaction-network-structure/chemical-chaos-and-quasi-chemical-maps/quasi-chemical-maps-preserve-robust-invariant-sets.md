# Quasi-chemical maps preserve robust invariant sets

**Setting.** A polynomial dynamical system (DS) $\dot{\mathbf{x}} = \mathbf{f}(\mathbf{x})$ on $\mathbb{R}^N$ is *chemical* (a CDS) if it is the mass-action ODE of some reaction network, i.e. every negative term of $f_i$ contains the factor $x_i$, so that the positive orthant is invariant. A *quasi-chemical map* (QCM) perturbs $\mathbf{f}$ by small polynomial terms $\mathbf{p}(\mathbf{x};\boldsymbol\mu)$, with coefficients smooth in parameters $\boldsymbol{\mu} > 0$ and vanishing uniformly on compacts as $\|\boldsymbol\mu\| \to 0$, and then translates by $\mathbf{T}(\boldsymbol\mu) \in \mathbb{R}^N_{>0}$, such that the result is chemical. Robust (structurally stable) invariant sets of the DS persist under such maps.

**Theorem (universal QCM).** Every $N$-dimensional degree-$n$ DS with exactly $M_n$ monomials of degree $n$ maps via a QCM to an $N$-dimensional degree-$(n+1)$ CDS with exactly $M_{n+1} = M_n$ monomials of degree $n+1$.

**Degree-preserving refinements.**
- Every linear DS with $M_1^-$ non-chemical first-degree monomials maps to a quadratic CDS with $M_2 \le M_1^- + N$ quadratic monomials.
- Every quadratic DS with $M_2$ quadratic monomials maps, after permutations and reflections of variables and a QCM, to a cubic CDS with $M_3 \le M_2 - 1$ cubic monomials.

**Theorem (chaos in low degree).** If an $N$-dimensional quadratic DS with one quadratic monomial has a robust bounded invariant set whose properties $\mathcal{P}$ are invariant under permutations, reflections and translations, then some $N$-dimensional quadratic CDS has a bounded invariant set in $\mathbb{R}^N_{>0}$ with properties $\mathcal{P}$. With two quadratic monomials the same holds for a cubic CDS with at most one cubic monomial. Explicit three-species instances include a chemical Rössler system (a quadratic CDS from a 9-reaction network), one-wing, two-wing (Lorenz-type) and hidden chaotic attractors.

## Depends on

- [Unique complex-balanced equilibrium of a deficiency-zero network](../../complex-balancing-and-the-deficiency-zero-theore/exists-unique-equilibrium-of-deficiency.md)

## Expansion

A negative monomial $-c\,x^{\alpha}$ in $f_i$ without the factor $x_i$ is "cross-negative" and cannot come from a reaction. Multiplying it by $(1 + \mu x_i)$-type factors and translating the attractor into the positive orthant turns it into a chemically admissible term while changing the vector field only by $O(\mu)$ on compacts, so hyperbolic or otherwise robust structures survive. Doing this term by term raises the degree by one in general, but when there are few quadratic terms a reflection can make one of them chemical for free, keeping the network quadratic. Complex-balanced (for example weakly reversible deficiency-zero) networks have a strict Lyapunov function on each stoichiometric class and so cannot be chaotic; such constructions necessarily use networks outside that class.

## Sources

- T. Plesa and J. C. Sprott, "Simple chemical systems with chaos", *Chaos: An Interdisciplinary Journal of Nonlinear Science* 36(5) (2026), 053135, Definition of the quasi-chemical map, Theorems 3.1-3.3 and Theorems 4.1-4.6, <https://doi.org/10.1063/5.0323112> (preprint arXiv:2511.15554).
