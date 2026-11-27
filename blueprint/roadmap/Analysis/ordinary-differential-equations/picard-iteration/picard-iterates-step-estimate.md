# Step estimate for Picard iterates

Let $E$ be a real normed space, let
$f : \mathbb{R} \times E \to E$ be continuous, and let $L \ge 0$ be such that $f(t, \cdot)$ is
$L$-Lipschitz for every $t \in \mathbb{R}$. Fix $t_0 \in \mathbb{R}$ and $x_0 \in E$, and let
$(u_n)_{n \ge 0}$ be maps $\mathbb{R} \to E$ with $u_0(t) = x_0$ and
$u_{n+1}(t) = x_0 + \int_{t_0}^{t} f(s, u_n(s))\,ds$ for all $n$ and $t$. If $M$ is a real number
with $\|f(s, x_0)\| \le M$ for every $s \in \mathbb{R}$, then for every $n \ge 0$ and every
$t \in \mathbb{R}$, $\|u_{n+1}(t) - u_n(t)\| \le M L^n |t - t_0|^{n+1} / (n+1)!$.

The integral is the Bochner integral, which is taken to be $0$ when $E$ is not complete.

Proof: Induct on the iterate index, apply the Lipschitz bound under the interval integral, and
integrate the absolute-power majorant exactly, as in the induction for estimate (2.29) in the proof
of Teschl, Theorem 2.5 (Section 2.3).

## Sources

- G. Teschl, Ordinary Differential Equations and Dynamical Systems, Section 2.3.
