# Basic reproduction number on a dynamic partnership network

On the binding-site partnership network of [Binding-site partnership network and its stationary degree distribution](binding-site-partnership-network-and-its-stationary-degree-distribution.md), superimpose an SI infection transmitted within each susceptible–infected partnership at rate $\beta > 0$; infected individuals stay infectious until death. Track binding sites of infected individuals in the linearized (early-epidemic) system by state: $A$ (free), $B_k$ (occupied by a susceptible partner who has $k$ partners), and $C$ (occupied by an infectious partner). Under the **mean field at distance one** closure, a susceptible partner of a newly infected individual is assumed to have $k$ partners with probability $Q_k$. The linearized binding-site dynamics are $\dot X = (T + \Sigma)X$ on $X = (X_A, X_{B_1}, \dots, X_{B_n}, X_C)$, where $\Sigma$ collects transitions and deaths (a matrix with non-negative off-diagonal entries and invertible, with $-\Sigma^{-1} \ge 0$) and $T \ge 0$ collects transmissions. Every column of $T$ is $\beta\,\phi_j$ or $0$, with

$$\phi_j = (n-j)\,\psi_A + (j-1)\,\psi_B + \psi_C, \qquad \psi_A = e_A,\ \psi_B = (0, Q_1, \dots, Q_n, 0)^{\top},\ \psi_C = e_C,$$

describing the $n$ sites of an individual just infected while having $j$ partners.

**Theorem 1.** $R_0$, defined as the dominant eigenvalue of the next-generation matrix $T(-\Sigma)^{-1}$, is a threshold parameter for the zero state of $\dot X = (T+\Sigma)X$: $\operatorname{sgn}(R_0 - 1) = \operatorname{sgn}(r)$, where $r$ is the dominant eigenvalue of $T + \Sigma$.

**Theorem 2.** Define the $3\times 3$ matrix $K = (k_{xy})_{x,y\in\{A,B,C\}}$ by $T(-\Sigma)^{-1}\psi_y = \sum_x k_{xy}\psi_x$. Then $R_0$ is also the dominant eigenvalue of $K$; $k_{xy}$ is the expected number of newly infected binding sites of type $x$ produced by one newly infected binding site of type $y$. Further reduction gives $R_0$ as the dominant eigenvalue of an explicit $2\times 2$ matrix, and the same $R_0$ arises from the $n \times n$ next-generation matrix on individuals indexed by their number of partners at infection.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Binding-site partnership network and its stationary degree distribution](binding-site-partnership-network-and-its-stationary-degree-distribution.md)

## Proof depends on

- [Next-generation threshold for stability of the disease-free equilibrium](../../next-generation-matrix-and-the-basic-reproductio/is-hurwitz-sub-iff-r0-lt-one.md)
- [Next-generation threshold for instability of the disease-free equilibrium](../../next-generation-matrix-and-the-basic-reproductio/exists-re-pos-iff-one-lt-r0.md)

## Expansion

Theorem 1 is the standard next-generation threshold for a positive-off-diagonal splitting $T + \Sigma$ with $\Sigma$ stable, proved via Perron–Frobenius theory. For Theorem 2, the range of $T$ is spanned by the three independent vectors $\psi_A, \psi_B, \psi_C$, so every eigenvector of $T(-\Sigma)^{-1}$ with nonzero eigenvalue lies in that span; writing $v = \sum_y w_y \psi_y$ turns $T(-\Sigma)^{-1}v = \lambda v$ into $K w = \lambda w$, so the nonzero spectra coincide. The closure makes the model approximate: for $n = 2$, partner states are not independent, so the binding-site description is a moment closure rather than an exact reduction of the network process. When $n = 1$ the model reduces to a pair-formation model.

## Sources

- K. Y. Leung, M. Kretzschmar, O. Diekmann, "SI infection on a dynamic partnership network: characterization of $R_0$", Journal of Mathematical Biology 71(1) (2015) 1–56, Section 5, Eqs. (32)–(36), Theorems 1 and 2, and Appendix C, <https://doi.org/10.1007/s00285-014-0808-5>, PMCID PMC4430681.
