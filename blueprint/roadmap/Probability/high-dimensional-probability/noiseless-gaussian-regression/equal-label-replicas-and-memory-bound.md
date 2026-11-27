# Posterior replica identities and Gaussian streaming information bounds

Use Euclidean rows $A\in(\mathbb R^d)^k$ of law $\gamma_k$ (independent standard Gaussians), labels $Ax$, and a base measure $\mu_0$ that is either standard Gaussian or normalized sphere measure. For $A$ of full row rank let $L_Ay=A^{\mathsf T}(AA^{\mathsf T})^{-1}y$, $v(x)=x-L_AAx$. The explicit base fiber law $F_{A,y}$ is the law of $L_Ay+v(G)$ for Gaussian base, or $L_Ay+\sqrt{1-\|L_Ay\|^2}\,v(G)/\|v(G)\|$ for sphere base, with $G$ standard Gaussian and totalized real square root and division. The base label density is

$$
\frac{(2\pi)^{-k/2}e^{-\|L_Ay\|^2/2}}{\sqrt{\det AA^{\mathsf T}}}
\quad\text{or}\quad
\frac{\Gamma(d/2)(1-\|L_Ay\|^2)^{(d-k-2)/2}}{\pi^{k/2}\Gamma((d-k)/2)\sqrt{\det AA^{\mathsf T}}},
$$

respectively, the sphere formula restricted to $\|L_Ay\|<1$ and zero outside; both are zero at deficient row rank. For measurable bounded nonnegative $f$, let $\nu=f\mu_0$, $D(A,y)$ be base density times $\int f\,dF_{A,y}$, and $F^f_{A,y}$ be the normalized tilted fiber, with point mass at zero when the tilt has zero mass.

For $k,m\ge1$ and $k+m\le d-2$, the measure integrating $D(A,y)^{m+1}$ against $\gamma_k\otimes dy$ and then drawing $m+1$ conditionally IID replicas $u_i$ from $F^f_{A,y}$ has finite mass. For every measurable nonnegative extended test of $(A,y,u)$ the integral equals the integral obtained from $\nu^{\otimes(m+1)}$, with weight $(2\pi)^{-km/2}V(u)^{-k}$, where $V$ is the Gram volume of $(u_i-u_0)_{i=1}^m$ and inversion is extended. In the latter integral use independent standard Gaussian rows projected orthogonally onto the complement of their difference span and set $y=Au_0$.

The explicit density, liminf of normalized open Euclidean label ball averages of radii $1/(n+1)$, and liminf of Gaussian convolution densities of the same standard deviations are jointly measurable. For every full-row-rank array they are versions of the pushed-forward density, agreeing almost everywhere in $y$. Moreover for almost every $u$ under $\nu^{\otimes(m+1)}$ the realized differences are linearly independent over $\mathbb R$; for almost every constrained row array given that $u$, its realized rows are also linearly independent over $\mathbb R$, all replicas have equal labels, the label lift in the spherical case has norm less than one, and all three densities at the common label agree and are positive finite.

For the regularized densities in these versions, take the lower limit in the extended nonnegative reals, including the source's extended reciprocal of the open-ball volume before multiplying the projected ball mass. The explicit density is the base density times the nonnegative lower integral of the bounded weight against the explicit base fiber, including the stated zero-mass fallback for the normalized tilt. No arbitrary conditional-probability version may replace these pointwise formulas under the equal-label comparison measure.

For the information clauses take a probability $f\sigma_d$, a finite nonempty message alphabet, and a randomized measurable rule of Gaussian rows and their exact labels producing $W$. Use $I(S;W\mid B,BS)$ where the side rows $B$ are independent of signal and experiment, with conditional information defined by KL against the product of conditional marginals. The following estimates use nats and extended nonnegative results, with all row counts rounded down unless a multiple of an already rounded count is specified.

* Gaussian bound: for sufficiently large $d$, $k=2\lfloor d/16\rfloor$, side width $4k$, and $0\le f\le L$, some absolute $C>0$ gives $I\le H(W)/(k+1)+Cd+C\log(2+\log L)$.
* Distance bound: for sufficiently large $d$, original and side widths $\lfloor d/16\rfloor,\lfloor d/2\rfloor$ and $f\le e^b$ with $b\ge0$ give $I\le H(W)/\lfloor d/8\rfloor+C(d+b/d)$.
* Haar bound: for $d\ge64$, start with any joint law of a uniform sphere signal and finite nonempty old state $U$, then update to $W$ by a Markov kernel of $U$ and $\lfloor d/16\rfloor$ fresh Gaussian rows with labels. Use $\lfloor d/4\rfloor$ independent side rows obtained by normalized Gram–Schmidt on independent Gaussian rows and condition additionally on $U$. Then $I(S;W\mid U,B,BS)\le H(W\mid U)/(\lfloor d/16\rfloor+1)+Cd+\log(1+Cd+H(U))+C[H(U)+\log d]/d^2$ for one absolute $C>0$.
* Synthetic bound: for $d\ge16$, widths $\lfloor d/8\rfloor,\lfloor d/2\rfloor$, a deterministic measurable $N$-valued message, and $0\le f\le L$ with $L\ge1$ give $I\le\log N/\lfloor d/8\rfloor+C[d+\log(1+\log L)]$.
* Incidence bound: for sufficiently large $d$, widths $\lfloor d/16\rfloor,\lfloor d/4\rfloor$, any randomized Markov message with $N\ge1$ possible values, and $0\le f\le F$ with $F\ge1$ give $I\le\log N/\lfloor d/16\rfloor+Cd+C\log(1+\log F)$.

Finally there is $c>0$ such that for every $M(d)=o(d^2)$ and all sufficiently large $d$, any completed-kernel learner with $2^{M(d)}$ states, independent seed, initial and transition laws of the stopping bit and next state, and a probability distribution of unit outputs depending only on terminal time/state, needs $T\ge c d\log(1/\epsilon)$ to achieve uniform-prior angular success at least $2/3$ for $0<\epsilon\le1/10$. At each time/state the transition is a Markov kernel on observations completed under Gaussian row times Lebesgue label. The experiment is required to supply a jointly measurable Markov output kernel agreeing almost everywhere in seed, uniform signal and Gaussian rows with the iterated learner law for that seed. The relevant success is for this joint kernel.

**Conventions.** Use explicit tilted projection fibers for two base laws, conditional KL, Gram and projected-row laws, and completed-kernel streaming semantics with independent seed and exact labels.

## Depends on

- [Conditional information from marginal kernels](conditional-information-from-marginal-kernels.md)
- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof depends on

Equal-label coarea, density-version agreement under the singular comparison measure (not just Lebesgue-almost-everywhere agreement in labels), five distinct replica information comparisons, and a finite-state block-to-precision argument.

## Expansion

Separate the measure identity and its density-version refinements, then treat the distinct row widths, priors and Gaussian versus Haar conditioning in the five information bounds. Only then lift the bound to the joint kernel experiment. Keep the stated two-thirds success threshold.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PosteriorReplicas.lean#L447-L452)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Posterior replicas and conditional information in Gaussian regression](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Posterior-replicas-and-conditional-information-in-Gaussian-regression-September-27-2026/paper.pdf)
