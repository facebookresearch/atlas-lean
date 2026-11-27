# One-zero continuous circle weight with only trivial invariant projections

Let $X=\mathbb R/\mathbb Z$ with normalized Haar measure and $H=\ell_2(\mathbb Z^2;\mathbb C)$. There exist $0<\theta<1$ irrational, unitaries $U,V$ on $H$, a vector $e\in H$ and continuous $f:X\to[0,1]$ with precisely one zero $z\in X$. They satisfy $VU=e^{2\pi i\theta}UV$ and $\langle e,U^mV^ne\rangle=1$ at $(m,n)=(0,0)$ and $0$ otherwise for integers $m,n$, and the linear span of these orbit vectors is dense in $H$. The integral of $-\log f$ is $+\infty$ with cost $+\infty$ at its zero.

Identify $X$ with the unit circle by $x\mapsto e^{2\pi i x}$. Transfer $f$ by this identification and extend its value by zero off the unit circle in the continuous functional calculus call at $V$. With $T=Uf(V)$, every star projection $p$ in the commutant of the commutant of $\{U,V\}$ satisfying $(1-p)Tp=0$ is $0$ or $1$. The angle and zero are existential; there is no separate operator-spectrum conclusion in this endpoint.

## Depends on

- Tracial rotation relations, Haar measure and continuous functional calculus of a unitary on its circle spectrum.

## Proof depends on

- A single concrete tracial rotation and continuous one-zero weight, and the absence of nontrivial invariant projections in the generated algebra.

## Expansion

Establish the unitary/cyclic moment model, verify the logarithmic divergence without mistaking the null singleton for the integral, and prove the projection obstruction for the constructed weighted rotation.

## Sources

- OpenAI, [ContinuousCircleWeight comparator, main_theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContinuousCircleWeight.lean#L50-L52).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/293.md).
