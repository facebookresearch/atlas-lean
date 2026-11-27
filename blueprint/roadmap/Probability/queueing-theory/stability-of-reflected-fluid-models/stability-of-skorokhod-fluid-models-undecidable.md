# Stability of fluid models of the Skorokhod problem is undecidable

No algorithm decides, given a starting state, a drift vector and a completely-S reflection matrix, whether every fluid path of the corresponding Skorokhod problem converges to the origin; this holds already for integer data.

**The Skorokhod problem.** For a real $d \times d$ matrix $R$, the Skorokhod problem asks, for each continuous $x : [0, \infty) \to \mathbb{R}^d$, for continuous $y, z : [0, \infty) \to \mathbb{R}^d$ with $z(t) \in \mathbb{R}^d_{+}$ such that

$$
z(t) = x(t) + R\, y(t), \qquad y(0) = 0,\ \ y_j \text{ non-decreasing}, \qquad \int_0^\infty z_j(s)\, dy_j(s) = 0 \quad (j = 1, \dots, d),
$$

so that $y_j$ increases only while $z_j = 0$. A matrix is an *S-matrix* if $Rw > 0$ coordinatewise for some $w \ge 0$, and *completely-S* if every principal submatrix is an S-matrix; a Skorokhod map exists exactly when $R$ is completely-S (Bernard and El Kharroubi; Taylor and Williams). For $z_0 \in \mathbb{R}^d_+$ and $\theta \in \mathbb{R}^d$, the solutions with input $x(t) = z_0 + \theta t$ are the *fluid paths* of the *fluid model* $(z_0, \theta, R)$, which is *stable* if every such solution satisfies $z(t) \to 0$ as $t \to \infty$.

**Theorem (Gamarnik and Katz).** There is no algorithm that, given $z_0 \in \mathbb{R}^d_+$, $\theta \in \mathbb{R}^d$ and a completely-S matrix $R$, decides whether the fluid model $(z_0, \theta, R)$ is stable (Theorem 5 of the source).

The instances built in the proof have integer data: $R \in \mathbb{Z}^{d \times d}$, an integer drift vector and a starting state with nonnegative integer entries, so the problem is undecidable already for integer inputs. Global stability of $(\theta, R)$ for every starting state, and positive recurrence of the semimartingale reflected Brownian motion with data $(\theta, \Sigma, R)$, are decidable when $d \le 3$; the source conjectures that both are undecidable in general dimension.

## Depends on

None.

## Proof depends on

- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

The proof reduces the halting problem for counter machines with two counters. For a machine with $m$ states it builds a Skorokhod problem of dimension $5m + 9$ whose fluid path, started from the point encoding the initial configuration, passes through the encodings of successive configurations at times $0, 5, 10, \dots$; two coordinates carry the counter values and others mark the current state. A final modification of $R$ in the column of the halting state makes the fluid path reach $0$ (by time $5T + 1$ if the machine halts at step $T$) exactly when the machine halts, and stay away from $0$ otherwise (Proposition 2 of the source). That the constructed matrix is completely-S is Proposition 1. The simulation of counter machines by fluid paths has no page.

## Sources

- D. Gamarnik and D. Katz, "The stability of the deterministic Skorokhod problem is undecidable", Queueing Systems 79 (2015), no. 3–4, 221–249, https://doi.org/10.1007/s11134-014-9424-8; read in arXiv:1007.1694v1 (Section 2, Theorem 5, Section 4 and Propositions 1 and 2 of arXiv:1007.1694v1, where theorems and propositions are numbered separately).
