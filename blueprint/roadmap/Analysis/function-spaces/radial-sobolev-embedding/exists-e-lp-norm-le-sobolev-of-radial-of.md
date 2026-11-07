# Radial Sobolev embedding outside the unit ball

Let $n \ge 2$, let $B$ be the closed unit
ball of $\mathbb{R}^n$, and let $1 < p < 2$ and $p \le q \le \infty$. Then there is a constant
$C > 0$ such that every radial function $f \colon \mathbb{R}^n \to \mathbb{R}$ that has compact
support, whose closed support is contained in $\mathbb{R}^n \setminus B$, and which is $C^\infty$
on $\mathbb{R}^n \setminus B$, satisfies

$$\|f\|_{L^q} \le C \left( \|f\|_{L^p} + \big\| |Df| \big\|_{L^p} \right),$$

where the norms are taken with respect to Lebesgue measure and $|Df(x)|$ is the operator norm of
the derivative of $f$ at $x$.

Smoothness here means $C^\infty$. The source's formal statement asked for real-analyticity
instead, which makes the claim vacuous: an analytic, radial, compactly supported $f$ vanishes
outside the ball.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear function spaces and their duals), problem `ma_proofbench_l2_80`, with the change above.
