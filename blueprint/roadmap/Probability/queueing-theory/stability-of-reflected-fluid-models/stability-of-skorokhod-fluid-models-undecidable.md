# Stability of fluid models of the Skorokhod problem is undecidable

No algorithm decides, given an integer starting state, drift vector and completely-S reflection matrix, whether every fluid path of the corresponding Skorokhod problem converges to the origin.

**The Skorokhod problem.** For a real $d \times d$ matrix $R$, the Skorokhod problem asks, for each continuous $x : [0, \infty) \to \mathbb{R}^d$ with $x(0) \in \mathbb{R}^d_+$, for continuous $y, z : [0, \infty) \to \mathbb{R}^d$ with $z(t) \in \mathbb{R}^d_{+}$ such that

$$
z(t) = x(t) + R\, y(t), \qquad y(0) = 0,\ \ y_j \text{ non-decreasing}, \qquad \int_0^\infty z_j(s)\, dy_j(s) = 0 \quad (j = 1, \dots, d),
$$

so that $y_j$ increases only while $z_j = 0$. A matrix is an *S-matrix* if $Rw > 0$ coordinatewise for some $w \ge 0$, and *completely-S* if every principal submatrix is an S-matrix; a Skorokhod map, defined on these inputs, exists exactly when $R$ is completely-S (Bernard and El Kharroubi; Taylor and Williams; Theorem 1 of the source, which omits the condition $x(0) \in \mathbb{R}^d_+$ that $z(0) = x(0)$ forces). For $z_0 \in \mathbb{R}^d_+$ and $\theta \in \mathbb{R}^d$, the solutions with input $x(t) = z_0 + \theta t$ are the *fluid paths* of the *fluid model* $(z_0, \theta, R)$, which is *stable* if every such solution satisfies $z(t) \to 0$ as $t \to \infty$.

**Theorem (Gamarnik and Katz).** There is no algorithm that, given $d$, $z_0 \in \mathbb{Z}^d_{\ge 0}$, $\theta \in \mathbb{Z}^d$ and $R \in \mathbb{Z}^{d \times d}$ promised to be completely-S, decides whether the fluid model $(z_0, \theta, R)$ is stable, that is, whether every real fluid path from $z_0$ tends to $0$ (Theorem 5 of the source, with its proof in Sections 4–6).

The source states Theorem 5 for real data $z_0 \in \mathbb{R}^d_+$, $\theta \in \mathbb{R}^d$ and real $R$; the instances its proof builds are integral ($\theta \in \{-1, 0\}^d$, $R$ integral also after the modification of Section 6, and $z_0$ with nonnegative integer entries), which gives the integer statement above. When $d \le 3$, the semimartingale reflected Brownian motion with data $(\theta, \Sigma, R)$ and non-singular covariance $\Sigma$ is positive recurrent exactly when $(\theta, R)$ is globally stable (stable for every starting state), and global stability can be verified by checking a system of equalities and inequalities (Theorem 4 of the source); the source conjectures that both problems are undecidable in general dimension.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for counter machines with two counters. For a machine with $m$ states it builds a Skorokhod problem whose dimension is linear in $m$ (the coordinates fall into groups of sizes $5, m, 2, 2, 4m, 4m$) and whose fluid path, started from the point encoding the initial configuration, passes through the encodings of successive configurations at times $0, 5, 10, \dots$; two coordinates carry the counter values and others mark the current state. A final modification of $R$ in the column of the halting state makes the fluid path reach $0$ (by time $5T + 1$ if the machine halts at step $T$) exactly when the machine halts, and stay away from $0$ otherwise (Proposition 2 of the source). That the constructed matrix is completely-S is Proposition 1. A good expansion adds and links pages for the simulation of counter machines by fluid paths and for the reduction to reaching a given state with both counters equal to $1$ (Theorem 7 of the source).

## Sources

- D. Gamarnik and D. Katz, "The stability of the deterministic Skorokhod problem is undecidable", Queueing Systems 79 (2015), no. 3–4, 221–249, https://doi.org/10.1007/s11134-014-9424-8; read in arXiv:1007.1694v1, whose numbering is used (theorems, propositions and lemmas are numbered separately): Section 2 (the Skorokhod problem, Theorem 1, Definition 1 and Theorem 5), Section 3 (Theorems 6 and 7 on counter machines), Sections 4 and 5 (the construction and Theorem 8), and Section 6 (Propositions 1 and 2).
