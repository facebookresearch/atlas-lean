# Podelski–Rybalchenko certificates for linear ranking functions

Consider a single-path [linear-constraint loop](linear-constraint-loops.md) over rational variables $x = (x_1, \dots, x_n)$ whose transition polyhedron $Q \subseteq \mathbb{Q}^{2n}$ is given by $A'' x'' \le c''$, where $x'' = (x, x')$, $c'' \in \mathbb{Q}^m$ and $A'' = (A\ A')$ with $A$ and $A'$ rational $m \times n$ matrices acting on $x$ and on $x'$. Let $\vec\mu$ and $\vec\eta$ be row vectors of $m$ rational variables, and let $\Gamma$ be the system

$$\vec\mu, \vec\eta \ge 0, \qquad \vec\mu \cdot A' = 0, \qquad (\vec\mu - \vec\eta) \cdot A = 0, \qquad \vec\eta \cdot (A + A') = 0, \qquad \vec\eta \cdot c'' \le -1 .$$

Then $Q$ has a [linear ranking function](linear-ranking-functions.md) if and only if $\Gamma$ has a rational solution. If moreover $Q$ is nonempty, then more precisely $\rho(x) = \vec\lambda \cdot x + \lambda_0$ is a linear ranking function for $Q$ if and only if $\Gamma$ has a solution with $\vec\lambda = \vec\eta \cdot A'$ and $\lambda_0 \ge \vec\mu \cdot c''$. Since $\Gamma$ is a system of linear inequalities, existence of a linear ranking function for a rational single-path loop is decidable in polynomial time.

## Depends on

- [Linear-constraint loops](linear-constraint-loops.md)
- [Linear ranking functions](linear-ranking-functions.md)

## Proof depends on

- [Farkas' lemma for inequality systems](../../../../Geometry/convex-geometry/linear-programming/exists-nonneg-mul-vec-le-iff.md)
- [Linear programming is in P (Khachiyan)](../../../../TheoryOfComputation/polynomial-time-problems/linear-programming-feasibility/lp-in-p.md)

## Sources

- A. M. Ben-Amram and S. Genaim, "Ranking functions for linear-constraint loops", *Journal of the ACM* 61(4), Article 26, 2014, <https://doi.org/10.1145/2629488>, numbered as in the journal version (the revised arXiv:1208.4041v4, <https://arxiv.org/abs/1208.4041v4>, keeps this numbering and adds Lemma 5.31), Section 4.4, Theorem 4.20 (after Podelski and Rybalchenko, with the required decrease $1$ in the last inequality), and Section 4.5, Lemma 4.23, stated under the standing assumption of Section 2.2 that the transition polyhedron does not contain the origin and so is not a cone ($m \ge 1$ in its generator representation), in particular nonempty.
