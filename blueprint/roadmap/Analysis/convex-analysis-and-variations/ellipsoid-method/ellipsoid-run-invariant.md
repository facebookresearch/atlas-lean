# Invariant of the ellipsoid method

Consider a run of the central-cut ellipsoid method for a set $P \subseteq \mathbb{R}^n$, $n \ge 2$: ellipsoids $E_k = E(a_k, A_k)$ with $A_0$ positive definite and $P \subseteq E_0$, such that whenever the centre $a_k$ is not in $P$ there is $c_k \ne 0$ with $c_k^\top x \le c_k^\top a_k$ for all $x \in P$, and $E_{k+1}$ is the [central-cut ellipsoid](next-matrix.md) of $E_k$ and $c_k$. If $a_0, \dots, a_{k-1} \notin P$, then $A_k$ is positive definite, $P \subseteq E_k$, and

$$
\mathrm{vol}\, E_k \le e^{-k/(2(n+1))}\, \mathrm{vol}\, E_0 .
$$

By induction: the [central-cut matrix is positive definite](next-matrix-pos-def.md), $P \subseteq E_k \cap \{c_k^\top x \le c_k^\top a_k\} \subseteq E_{k+1}$ by [the containment of the half-ellipsoid](half-ellipsoid-subset-next-ellipsoid.md), and each step shrinks the volume by the [volume lemma](volume-next-ellipsoid-lt.md). The separation oracle is abstract: any valid inequalities through the centres.

## Sources

- M. X. Goemans, *Lecture notes on the ellipsoid algorithm*, MIT 18.433 Combinatorial Optimization, Handout 19 (4 May 2009), <https://math.mit.edu/~goemans/18433S09/ellipsoid.pdf>, the algorithm and the remark after Claim 7.2.
