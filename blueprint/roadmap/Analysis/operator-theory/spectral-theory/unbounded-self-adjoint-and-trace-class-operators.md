# Spectral theorem for unbounded self-adjoint operators, and trace-class operators

This node is still to be broken down. It covers the Hilbert-space operator theory that the pages on the
coefficients of square-integrable representations and on distribution characters use.

- **Spectral theorem.** Let $A$ be a self-adjoint operator, possibly unbounded, with domain $D(A)$ on a
  separable Hilbert space $\mathcal{H}$. There are a finite measure space $(M, \mu)$, a unitary operator
  $U \colon \mathcal{H} \to L^2(M, \mu)$ and a real-valued measurable function $f$ on $M$, finite almost everywhere,
  such that $\psi \in D(A)$ if and only if $f \cdot U\psi \in L^2(M, \mu)$, and $UAU^{-1}$ is multiplication by $f$
  on $U(D(A))$. Equivalently, $A = \int \lambda \, dP_\lambda$ for a unique projection-valued measure $P$ on
  $\mathbb{R}$, and bounded Borel functions $g$ define bounded operators $g(A)$ through a $*$-homomorphism;
  for $A \ge 0$ this gives the positive square root $A^{1/2}$.
- **Trace-class operators.** A bounded operator $A$ on a Hilbert space is trace class if $\operatorname{tr} \lvert A \rvert
  = \sum_n \langle \lvert A \rvert \varphi_n, \varphi_n \rangle < \infty$ for an orthonormal basis $(\varphi_n)$,
  where $\lvert A \rvert = (A^* A)^{1/2}$. The trace-class operators form a two-sided $*$-ideal of the bounded
  operators; for $A$ trace class, $\operatorname{tr} A = \sum_n \langle \varphi_n, A \varphi_n \rangle$ converges absolutely
  and does not depend on the orthonormal basis, $\operatorname{tr}$ is linear, and $\operatorname{tr}(AB) = \operatorname{tr}(BA)$ for
  every bounded $B$.

## Expansion

A good expansion has statement pages for the multiplication-operator, functional-calculus and
projection-valued-measure forms of the spectral theorem, and definition and statement pages for the trace
class and the trace, each citing the sources below with locators. Reed and Simon deduce the unbounded
spectral theorem from the bounded one applied to the resolvents $(A \pm i)^{-1}$.

## Depends on

- [Spectral theorem for bounded self-adjoint operators, multiplication form](spectral-theorem-for-bounded-self-adjoint-operat/bounded-self-adjoint-spectral-multiplica.md), for the setting of
  multiplication operators

## Proof depends on

- [Spectral theorem for bounded self-adjoint operators, multiplication form](spectral-theorem-for-bounded-self-adjoint-operat/bounded-self-adjoint-spectral-multiplica.md), applied to the
  resolvents

## Sources

- M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised and enlarged
  edition, Academic Press, 1980: §VI.6, pp. 206–212 (the trace class: the definition through $\operatorname{tr} \lvert A \rvert$,
  Theorem VI.19, the $*$-ideal, Theorem VI.24 and the definition of the trace, Theorem VI.25, linearity and
  $\operatorname{tr} AB = \operatorname{tr} BA$), and §VIII.3, pp. 259–264 (Theorem VIII.4, the spectral theorem in multiplication
  operator form on a separable Hilbert space; Theorem VIII.5, functional calculus form; Theorem VIII.6,
  projection-valued measure form).
