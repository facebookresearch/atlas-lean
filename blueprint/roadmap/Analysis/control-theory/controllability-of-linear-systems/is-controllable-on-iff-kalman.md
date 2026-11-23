# Kalman rank condition

Let $T > 0$. The system $\dot x = A x + B u$ on finite-dimensional real inner product spaces $E$, $U$ is controllable on $[0, T]$ if and only if

$$\operatorname{Span} \{ A^i B u : u \in U, \ 0 \le i < \dim E \} = E,$$

that is, $\operatorname{rank} [B, AB, \dots, A^{n-1} B] = n$ with $n = \dim E$. In particular, controllability on $[0, T]$ does not depend on $T > 0$.

This is Coron, *Control and Nonlinearity* (AMS 2007), Theorem 1.16, which Coron attributes to Kalman, Ho and Narendra (1963, Theorem 10), and Sontag, *Mathematical Control Theory* (2nd ed., 1998), Theorem 3. The proof follows Coron's: if $W_T \eta = 0$, the function $s \mapsto \langle \eta, e^{sA} B v \rangle$ vanishes on $[0, T]$, so do all its derivatives $\langle \eta, e^{sA} A^k B v \rangle$, and at $s = 0$ this gives $\eta \perp A^k B v$; conversely, a vector orthogonal to the Kalman subspace is orthogonal to every $A^k B v$ by Cayley–Hamilton, hence to every $e^{sA} B v$ by the exponential series, and lies in the kernel of $W_T$.

## Informally uses

- [Gramian criterion for controllability](is-controllable-on-iff-bijective-gramian.md): Coron derives the rank condition from Theorem 1.11.
- [Kalman rank condition, dual form](kalman-subspace-eq-top-iff.md): the Cayley–Hamilton reduction to powers below $\dim E$.

## Background

- [Pole placement for single-input systems](../pole-placement/exists-charpoly-add-smul-right-eq.md): the rank condition with one input says that $b$ is a cyclic vector of $A$, the hypothesis of pole placement.
