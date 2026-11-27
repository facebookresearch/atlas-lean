# Elgindi's theorem: finite-time singularity of $C^{1,\alpha}$ Euler flows

There exist a real number $\alpha > 0$ and a vector field $u_0 : \mathbb{R}^3 \to \mathbb{R}^3$ such that

- $u_0$ is [odd](is-odd.md) in the strong sense used here: for each $i$, the component $u_{0,i}$ is an odd
  function of the $i$-th coordinate and an even function of each of the other two;
- $u_0$ has divergence $0$ at every point;
- $u_0$ lies in [$C^{1,\alpha}(\mathbb{R}^3)$](is-cont-diff-holder.md): it is continuously differentiable and its
  derivative is bounded and globally $\alpha$-Hölder on $\mathbb{R}^3$ ($u_0$ itself need not be bounded);
- for some constant $C > 0$ its vorticity satisfies $|(\nabla \times u_0)(x)| \le C / (|x|^\alpha + 1)$ for
  every $x \in \mathbb{R}^3$;

and there exist functions $p : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}$ and
$u : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}^3$ such that

- $u(\cdot, t)$ is odd, in the same sense, for every $t \in [0, 1)$;
- $u$ is a [local solution of the incompressible Euler equations](is-local-euler-equation-solution.md) up to
  time $1$ with pressure $p$ and initial data $u_0$;
- for every $T \in (0, 1)$, $u$ lies in [$C^{1,\alpha}(\mathbb{R}^3 \times [0, T])$](is-cont-diff-holder-on.md) as a
  function of $(x, t)$: it is continuously differentiable there and its derivative within
  $\mathbb{R}^3 \times [0, T]$ is bounded and $\alpha$-Hölder on that set;
- the vorticity blows up in the Beale–Kato–Majda sense:

    $$\int_0^t \sup_{x \in \mathbb{R}^3} |(\nabla \times u(\cdot, s))(x)| \, ds \to +\infty \quad \text{as } t \to 1^-.$$

Here $|\cdot|$ is the Euclidean norm, differentiability is over $\mathbb{R}$, and
$\mathbb{R}^3 \times \mathbb{R}$ carries the norm $\max(|x|, |t|)$.

Elgindi states the conclusion for the unique local odd solution in this class. Uniqueness of
solutions up to any time $T$ at which they exist was already known, so only existence is
asserted here.

## Sources

- T. M. Elgindi, *Finite-time singularity formation for $C^{1,\alpha}$ solutions to the incompressible Euler equations on $\mathbb{R}^3$*, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_finite_time_singularity` of the lean-eval benchmark.
