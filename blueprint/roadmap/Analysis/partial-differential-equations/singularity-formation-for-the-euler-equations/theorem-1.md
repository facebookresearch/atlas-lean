# Elgindi's theorem: finite-time singularity of $C^{1,\alpha}$ Euler flows

There exist a
real number $\alpha > 0$ and a vector field $u_0 : \mathbb{R}^3 \to \mathbb{R}^3$ that is odd,
has divergence $0$ at every point and lies in $C^{1,\alpha}(\mathbb{R}^3)$, together with a
constant $C > 0$ such that its vorticity satisfies
$|(\nabla \times u_0)(x)| \le C / (|x|^\alpha + 1)$ for every $x \in \mathbb{R}^3$, and there
exist functions $p : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}$ and
$u : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}^3$ such that $u(\cdot, t)$ is odd for every
$t \in [0, 1)$, $u$ is a local solution of the incompressible Euler equations up to time $1$
with pressure $p$ and initial data $u_0$, $u$ lies in $C^{1,\alpha}(\mathbb{R}^3 \times [0, T])$
as a function of $(x, t)$ for every $T \in (0, 1)$, and

$$\int_0^t \sup_{x \in \mathbb{R}^3} |(\nabla \times u(\cdot, s))(x)| \, ds \to +\infty$$

as $t \to 1^-$. Here $|\cdot|$ is the Euclidean norm, differentiability is over $\mathbb{R}$, and
$\mathbb{R}^3 \times \mathbb{R}$ carries the norm $\max(|x|, |t|)$.

Elgindi states the conclusion for the unique local odd solution in this class. Uniqueness of
solutions up to any time $T$ at which they exist was already known, so only existence is
asserted here.

## Sources

- T. M. Elgindi, `Finite-time singularity formation for C^{1,α} solutions to the incompressible Euler equations on ℝ³`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge. Problem `annals_finite_time_singularity` of the lean-eval benchmark.
