# Reaching the origin under a fixed saturated linear map is undecidable

There are a dimension $n$ and a fixed integer matrix $A$ such that no algorithm decides, given a rational starting point, whether some iterate of the saturated linear map $x \mapsto \sigma(Ax)$ sends it to the origin.

Let $\sigma\colon \mathbb{R} \to \mathbb{R}$ be the saturation function

$$
\sigma(x) = \tfrac{1}{2}\bigl(|x| - |x - 1| + 1\bigr) = \begin{cases} 0, & x \le 0, \\ x, & 0 < x < 1, \\ 1, & x \ge 1, \end{cases}
$$

and, abusing notation, let $\sigma\colon \mathbb{R}^n \to \mathbb{R}^n$ apply it coordinatewise. For $A \in M_n(\mathbb{Z})$ the map $x \mapsto \sigma(Ax)$ is a rational piecewise affine map of $\mathbb{R}^n$, the update rule of a recurrent neural network with saturated-linear activation.

**Theorem (Siegelmann–Sontag).** There exist $n$ and a specific matrix $A \in M_n(\mathbb{Z})$ for which it is impossible to decide, given a starting point $\vec{a} \in \mathbb{Q}^n$, whether some iterate of the map $\vec{x} \mapsto \sigma(A\vec{x})$ maps $\vec{a}$ to $\vec{0}$.

The matrix, and hence the dimension, is fixed; only the starting point is the input. This is the form of the result recorded in the survey; it rests on the theorem that such neural networks can simulate a universal Turing machine.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Siegelmann and Sontag proved that finite recurrent networks of saturated-linear units with rational weights simulate Turing machines; applied to a universal machine, this gives a fixed network, that is a fixed matrix $A$, whose trajectories encode computations, with the halting of the machine on an input corresponding to the trajectory of an encoded rational starting point reaching $\vec{0}$. The undecidability of the halting problem of the universal machine then gives the statement. The simulation theorem has no page; the survey states the consequence without proof.

## Sources

- Bjorn Poonen, *Undecidable problems: a sampler*, in: Interpreting Gödel: Critical Essays (J. Kennedy, ed.), Cambridge University Press, 2014, pp. 211–241, https://doi.org/10.1017/CBO9780511756306.015, read in arXiv:1204.0299v2 (the function $\sigma$ defined in Section 9 and the statement in Section 10.1 of arXiv:1204.0299v2).
- H. T. Siegelmann and E. D. Sontag, *On the computational power of neural nets*, Journal of Computer and System Sciences 50 (1995), no. 1, 132–150, https://doi.org/10.1006/jcss.1995.1013, the original source, cited for attribution beside Bjorn Poonen's survey above.
