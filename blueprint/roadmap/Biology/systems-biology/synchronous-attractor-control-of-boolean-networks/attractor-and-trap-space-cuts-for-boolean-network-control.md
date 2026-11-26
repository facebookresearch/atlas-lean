# Attractor and trap-space cuts for Boolean network control

**Setting.** A Boolean network $f:\mathbb B^n\to\mathbb B^n$ is iterated synchronously, $x_{t+1}=f(x_t)$, so attractors are fixed points and cycles. A set $\mathcal C$ of genes is controllable; a control is $d=(d^0_j,d^1_j)_{j\in\mathcal C}$ with $d^0_j+d^1_j\le1$, where $d^k_j=1$ fixes gene $j$ to value $k$, producing the controlled network $f'_j\equiv k$ for fixed genes and $f'_i=f_i$ otherwise. An attractor is *forbidden* if it violates the phenotype (some state has the phenotype gene $x_\phi=0$). For a cycle $\hat x=(\hat x_1,\dots,\hat x_T)$ of the network under some control and a controllable gene $j$, define $\kappa_j=\hat x_{j,1}$, $\alpha_j=1$ iff $x_j$ is constant along the cycle, and $\beta_j=1$ iff $x_j$ obeys its own update rule $f_j$ at every step of the cycle.

**Theorem 4 (which controls keep a given cycle).** For a control $d$ with $d^0_j+d^1_j\le1$, $\hat x$ is an attractor of the network under $d$ if and only if $g_j(\hat x,d)=0$ for every $j\in\mathcal C$, where
$$g_j=d^{1-\kappa_j}_j\ \text{ if }\alpha_j\wedge\beta_j,\qquad g_j=1-d^{\kappa_j}_j\ \text{ if }\alpha_j\wedge\neg\beta_j,\qquad g_j=d^0_j+d^1_j\ \text{ if }\neg\alpha_j\wedge\beta_j.$$
A gene that is constant and consistent with its rule may be left free or fixed to its value; one that is constant against its rule must be fixed to its value; one that oscillates must be left free.

**Theorem 5 (attractor cut).** If the subproblem for candidate control $\hat d$ returns a forbidden attractor $\hat x$, then every feasible control satisfies
$$\sum_{j\in\mathcal C}\Big((1-\alpha_j)d^{\kappa_j}_j+\beta_jd^{1-\kappa_j}_j+(1-\beta_j)(1-d^{\kappa_j}_j)\Big)\ \ge1,$$
which removes $\hat d$ and every other control under which $\hat x$ remains an attractor.

**Theorems 6–7 (trap-space cut).** If a subspace $h$ (genes fixed to $0$, to $1$, or free) is a trap space under control $u$, it remains one under every control $d\ge u$ that never fixes a gene to the value opposite to the one $h$ fixes. Hence, if $h$ is fully forbidden (every state in it has $x_\phi=0$), every feasible control satisfies $\sum_j\sum_k\big(u^k_j(1-d^k_j)+(1-u^k_j)h^k_jd^{1-k}_j\big)\ge1$ for a long enough horizon. A trap space found by the subspace-separation integer program gives a valid cut that excludes the candidate (Theorem 8), and under a mild condition it implies the attractor cut of every attractor it contains (Theorem 9).

## Expansion

A cycle survives a control iff each fixed gene's constant value agrees with the cycle and each free gene follows its rule along the cycle; the three cases of Theorem 4 encode exactly this, and $\neg\alpha_j\wedge\neg\beta_j$ cannot occur for a cycle that exists under some control. Feasible controls must destroy every forbidden attractor, so the sum of the $g_j$ must be positive, which is the attractor cut written with the indicators. Trap spaces are forward-invariant subcubes and always contain an attractor, so a forbidden trap space is a certificate that excludes a whole family of controls at once, giving stronger cuts in a logic-based Benders decomposition.

## Sources

- K. Moon, K. Lee, L. Paulevé, "A Bilevel Integer Programming Approach for the Synchronous Attractor Control Problem", arXiv preprint (2026), Theorems 4–9, <https://doi.org/10.48550/arXiv.2604.01018>.
