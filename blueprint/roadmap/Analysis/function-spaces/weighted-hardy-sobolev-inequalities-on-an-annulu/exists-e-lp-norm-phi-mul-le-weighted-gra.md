# Critical weighted Sobolev inequality on an annulus

For $r > 0$ let $B_r$ be the open disc
of radius $r$ about the origin in the Euclidean plane $\mathbb{R}^2$, let
$\Omega_1 = B_3 \setminus \overline{B}_1$ and $\Omega_2 = B_3 \setminus \overline{B}_2$, and let
$\phi(x) = \max\{|x| - 1, 0\}$, the distance from $x$ to the closed unit disc. Let $1 \le p < 2$
and $p^* = 2p/(2-p)$. Then there is a real number $C > 0$ such that every function
$u \colon \mathbb{R}^2 \to \mathbb{R}$ that is continuously differentiable on $\Omega_1$ and for
which $\|\phi \nabla u\|_{L^p(\Omega_1)}$ and $\|u\|_{L^p(\Omega_2)}$ are finite satisfies

$$\|\phi u\|_{L^{p^*}(\Omega_1)} \le C\|\phi \nabla u\|_{L^p(\Omega_1)} + C\|u\|_{L^p(\Omega_2)}.$$

Here the norms are taken with respect to Lebesgue measure, $\|\phi \nabla u\|_{L^p(\Omega_1)}$ is
the $L^p(\Omega_1)$ norm of $x \mapsto \phi(x)\,|\nabla u(x)|$, and $\nabla u(x)$ is the derivative
of $u$ at $x$ within $\Omega_1$.

## Sources

- MA-ProofBench (L. Pu et al., arXiv:2606.13782), Level II (Functional analysis; Linear function spaces and their duals), problem `ma_proofbench_l2_65`.
