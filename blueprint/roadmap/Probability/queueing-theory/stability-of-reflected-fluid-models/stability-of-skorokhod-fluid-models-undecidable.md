# Stability of fluid models of the Skorokhod problem is undecidable

No algorithm decides, given a starting state, a drift vector and a completely-S reflection matrix, whether every fluid path of the corresponding Skorokhod problem converges to the origin; this holds already for integer data.

**The Skorokhod problem.** For a real $d \times d$ matrix $R$, the Skorokhod problem asks, for each continuous $x : [0, \infty) \to \mathbb{R}^d$, for continuous $y, z : [0, \infty) \to \mathbb{R}^d$ with $z(t) \in \mathbb{R}^d_{+}$ such that

$$
z(t) = x(t) + R\, y(t), \qquad y(0) = 0,\ \ y_j \text{ non-decreasing}, \qquad \int_0^\infty z_j(s)\, dy_j(s) = 0 \quad (j = 1, \dots, d),
$$

so that $y_j$ increases only while $z_j = 0$. A matrix is an *S-matrix* if $Rw > 0$ coordinatewise for some $w \ge 0$, and *completely-S* if every principal submatrix is an S-matrix; a Skorokhod map exists exactly when $R$ is completely-S (Bernard and El Kharroubi; Taylor and Williams). For $z_0 \in \mathbb{R}^d_+$ and $\theta \in \mathbb{R}^d$, the solutions with input $x(t) = z_0 + \theta t$ are the *fluid paths* of the *fluid model* $(z_0, \theta, R)$, which is *stable* if every such solution satisfies $z(t) \to 0$ as $t \to \infty$.

**Theorem (Gamarnik and Katz).** There is no algorithm that, given $z_0 \in \mathbb{R}^d_+$, $\theta \in \mathbb{R}^d$ and a completely-S matrix $R$, decides whether the fluid model $(z_0, \theta, R)$ is stable (Theorem 5 of the source).

The instances built in the proof have integer data: $R \in \mathbb{Z}^{d \times d}$, an integer drift vector and a starting state with nonnegative integer entries, so the problem is undecidable already for integer inputs. When $d \le 3$, the semimartingale reflected Brownian motion with data $(\theta, \Sigma, R)$ is positive recurrent exactly when $(\theta, R)$ is globally stable (stable for every starting state), and global stability can be verified by checking a system of equalities and inequalities (Theorem 4 of the source); the source conjectures that both problems are undecidable in general dimension.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for counter machines with two counters. For a machine with $m$ states it builds a Skorokhod problem whose dimension is linear in $m$ (the coordinates fall into groups of sizes $5, m, 2, 2, 4m, 4m$) and whose fluid path, started from the point encoding the initial configuration, passes through the encodings of successive configurations at times $0, 5, 10, \dots$; two coordinates carry the counter values and others mark the current state. A final modification of $R$ in the column of the halting state makes the fluid path reach $0$ (by time $5T + 1$ if the machine halts at step $T$) exactly when the machine halts, and stay away from $0$ otherwise (Proposition 2 of the source). That the constructed matrix is completely-S is Proposition 1. The simulation of counter machines by fluid paths, and the reduction to reaching a given state with both counters equal to $1$ (Theorem 7 of the source), have no page on main.

## Sources

- D. Gamarnik and D. Katz, "The stability of the deterministic Skorokhod problem is undecidable", Queueing Systems 79 (2015), no. 3–4, 221–249, https://doi.org/10.1007/s11134-014-9424-8; read in arXiv:1007.1694v1, whose numbering is used (theorems, propositions and lemmas are numbered separately): Section 2 (the Skorokhod problem, Theorem 1, Definition 1 and Theorem 5), Section 3 (Theorems 6 and 7 on counter machines), Sections 4 and 5 (the construction and Theorem 8), and Section 6 (Propositions 1 and 2).
