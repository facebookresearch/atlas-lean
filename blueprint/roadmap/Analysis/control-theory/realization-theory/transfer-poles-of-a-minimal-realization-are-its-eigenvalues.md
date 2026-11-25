# Transfer poles of a minimal realization are its eigenvalues

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $(A, B, C, D)$ be a realization with $A \in \mathbb{K}^{n \times n}$ whose triple $(A, B, C)$ is canonical, that is controllable and observable. Let $G(s) = C(sI - A)^{-1}B + D$ for complex $s \notin \operatorname{spec}(A)$, where the spectrum is taken over $\mathbb{C}$. Call $s_0 \in \mathbb{C}$ a pole of $G$ if $\|G(s)\|$ is unbounded on every punctured neighborhood of $s_0$. Then:

1. **Poles are eigenvalues.** $s_0$ is a pole of $G$ if and only if $s_0 \in \operatorname{spec}(A)$. Multiplicities are not compared.
2. **Stability.** $A$ is Hurwitz if and only if $G$ has no pole with $\operatorname{Re} s \ge 0$, and $A$ is convergent if and only if $G$ has no pole with $|s| \ge 1$.

Without canonicity only "every pole is an eigenvalue" holds. For $A = \operatorname{diag}(1, -1)$, $B = (0, 1)^\top$, $C = (0, 1)$, the transfer function is $1/(s + 1)$, while $1 \in \operatorname{spec}(A)$.

**Proof.**

- **No pole off the spectrum.** If $s_0 \notin \operatorname{spec}(A)$, then $s \mapsto (sI - A)^{-1}$ is continuous near $s_0$, so $G$ is bounded there.
- **Principal parts.** Work over $\mathbb{C}$. Let $\lambda$ be an eigenvalue, $P_\lambda$ the spectral projection onto its generalized eigenspace, and $m$ its index. Near $\lambda$,

    $$(sI - A)^{-1} = \sum_{j=0}^{m-1} (s - \lambda)^{-j-1} (A - \lambda I)^j P_\lambda + H(s),$$

    with $H$ holomorphic at $\lambda$. Hence $G(s) = \sum_{j<m} (s - \lambda)^{-j-1} M_j + (\text{holomorphic})$, where $M_j = C (A - \lambda I)^j P_\lambda B$. If some $M_j \ne 0$, take the largest such $j$. Then $\|G(s)\| \ge |s - \lambda|^{-j-1}\big(\|M_j\| - O(|s - \lambda|)\big) \to \infty$, so $\lambda$ is a pole.

- **Some $M_j$ is nonzero.** Suppose $M_j = 0$ for every $j$. Since $A^k P_\lambda = \sum_{j \le k} \binom{k}{j} \lambda^{k-j} (A - \lambda I)^j P_\lambda$, this gives $C A^k P_\lambda B = 0$ for all $k$. As $P_\lambda$ commutes with $A$, the space $P_\lambda \operatorname{span}\{A^k B u\}$ consists of vectors $v$ with $C A^i v = 0$ for all $i$. Controllability makes the span all of $\mathbb{C}^n$, and observability makes the only such $v$ zero. So $P_\lambda = 0$, contradicting that $\lambda$ is an eigenvalue. For $\mathbb{K} = \mathbb{R}$, controllability and observability are rank conditions, which persist over $\mathbb{C}$.
- **Part 2.** This follows from part 1.

## Depends on

- [Minimal realizations are exactly the canonical ones](minimal-realizations-are-canonical.md): canonical (controllable and observable) realizations, equivalently minimal ones

## Proof depends on

- [Jordan normal form](../../../LinearAlgebra/eigenvalues-and-canonical-forms/jordan-normal-form/exists-jordan-normal-form-of-splits.md): over $\mathbb{C}$ it gives the generalized-eigenspace decomposition, the spectral projections $P_\lambda$ and the displayed principal part of $(sI - A)^{-1}$

## Background

- [The transfer matrix as a rational function, and its invariance under similarity](transfer-matrix-as-a-rational-function-and-its-similarity-invariance.md): the transfer matrix as a rational function with denominator $\det(XI - A)$
- [Internal and external stability of minimal realizations](internal-and-external-stability-of-minimal-realizations.md): the impulse-response form of the same stability equivalence, and the same witness

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 9.5: for $G(s) = C(sI - A)^{-1}B + D$ the poles are the eigenvalues of $A$, the points where $\det(sI - A) = 0$ (p. 9-24); the source does not state the minimality hypothesis, which the cancellation witness shows is needed.
- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 6.5, Definition 6.5.9 and Theorem 27: minimal triples are exactly the canonical ones (pp. 286–287).
