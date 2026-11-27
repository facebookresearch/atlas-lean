# Lieb's concavity theorem, joint form

For a square complex matrix $K$ and reals $q, r \ge 0$ with $q + r \le 1$, the map $(A, B) \mapsto \operatorname{Re} \operatorname{tr}(K^* A^q K B^r)$ is jointly concave on pairs of positive definite matrices, where $A^q$ is defined by the functional calculus (E. A. Carlen, *Trace inequalities and quantum entropy: an introductory course*, lecture-notes draft of May 3, 2009, Theorem 6.1, the case of square $K$; E. H. Lieb, Adv. Math. 11 (1973), 267–288). The trace is real, being the squared Hilbert–Schmidt norm of $A^{q/2} K B^{r/2}$.

For fixed $B$ (take $r = 0$) the concavity in $A$ alone already follows from the operator concavity of $t \mapsto t^q$, $0 \le q \le 1$ ; the content of the theorem is the *joint* concavity in the pair $(A, B)$. The bound $q + r \le 1$ cannot be dropped: already for $1 \times 1$ matrices and $K = 1$ the map $(a, b) \mapsto a^q b^r$ is jointly concave on $(0, \infty)^2$ only when $q + r \le 1$.

Carlen's notes give Ando's tensor-product proof. Taking $K = I$, $q = 1 - p$, $r = p$ and differentiating at $p = 0$ gives the joint convexity of the relative entropy $(A, B) \mapsto \operatorname{tr} A \log A - \operatorname{tr} A \log B$ (Carlen, Theorem 6.3), from which monotonicity of relative entropy under partial traces and strong subadditivity follow (Carlen, Theorems 6.4 and 6.6).

**Proof.** For $q, r > 0$, Ando's form of the theorem gives the joint concavity of $(B, A) \mapsto \operatorname{Re} \operatorname{tr}(B^r K^* A^q K)$ on strictly positive operators of a finite-dimensional Hilbert space; the trace is the same by cyclicity. The ⋆-algebra isomorphism between $n \times n$ matrices and operators on $\mathbb{C}^n$ preserves spectra and traces and commutes with the functional calculus, so the statement transfers. The boundary cases $q = 0$ and $r = 0$ are the one-variable cases below. Carlen states the theorem for a rectangular $m \times n$ matrix $K$; the rectangular case reduces to the square one by padding $K$ with zeros. Theorem numbers refer to the lecture-notes draft of May 3, 2009.

## Informally uses

- [Lieb's concavity theorem, case `r = 0`](lieb-concavity-trace-rpow-of-right-eq-ze.md): the boundary case $r = 0$.
- [Lieb's concavity theorem, case `q = 0`](lieb-concavity-trace-rpow-of-left-eq-zer.md): the boundary case $q = 0$.

## Background

- [Lieb's concavity theorem](lieb-concavity.md): the exponential form $A \mapsto \operatorname{tr}\exp(H + \log A)$, from the same 1973 paper.
- [The square is operator convex](../../../Analysis/operator-algebras/operator-monotone-and-operator-convex-functions/sq-convex-comb-le.md): an example of operator convexity, the operator-level notion behind the one-variable concavity of $t^q$.

## Sources

- E. A. Carlen, Trace inequalities and quantum entropy: an introductory course, lecture-notes draft of May 3, 2009 (published in Entropy and the Quantum, Contemp. Math. 529, Amer. Math. Soc., 2010, 73–140), Theorem 6.1.
- Physlib, `QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LiebAndoTrace.lean`, `LiebAndoTrace.liebExtensionTrace_jointlyConcaveOn_pdSet`.
- E. H. Lieb, Convex trace functions and the Wigner–Yanase–Dyson conjecture, Adv. Math. 11 (1973), 267–288.
