# Internal and external stability of minimal realizations

Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, and let $(A, B, C)$ with $A \in \mathbb{K}^{n \times n}$, $B \in \mathbb{K}^{n \times m}$ and $C \in \mathbb{K}^{p \times n}$ be **canonical**: controllable and observable, $\operatorname{rank} R(A, B) = n$ and $\operatorname{rank} O(A, C) = n$. Equivalently, it is a minimal realization of its Markov sequence.

1. **Continuous time.** $A$ is Hurwitz (every eigenvalue has negative real part) if and only if the impulse response $K(t) = C e^{tA} B$ is integrable on $[0, \infty)$, $\int_0^\infty \|C e^{tA} B\| \, dt < \infty$.
2. **Discrete time.** $A$ is convergent (every eigenvalue has modulus less than $1$) if and only if the impulse response $K_k = C A^{k-1} B$, $k \ge 1$, is summable, $\sum_{k \ge 1} \|C A^{k-1} B\| < \infty$.

Use Euclidean vector norms and their induced matrix operator norms. In continuous time inputs are measurable and essentially bounded, with the essential-supremum norm; in discrete time they are bounded sequences. Integrability (summability) of the impulse response is equivalent to **uniform bounded-input bounded-output stability**. The zero-state convolution output satisfies $\|y\|_\infty \le \|K\|_1 \|u\|_\infty$, and conversely a finite uniform bound for all such inputs forces $K$ to be integrable (summable). For necessity, isolate one input/output coordinate and, at each finite horizon, choose the time-reversed sign of that kernel entry (its conjugate phase over $\mathbb C$); the output bounds the integral or sum of its absolute value. There are finitely many entries, so entrywise integrability is equivalent to matrix-norm integrability.

The forward implication needs no canonicity: the exponential or geometric bound on the state-transition matrices gives the integrability or summability of the kernel. This includes singular discrete-time matrices: zero-eigenvalue Jordan blocks contribute only a finite transient, not terms of the form $k^l\lambda^k$ for every $k$.

For the continuous-time converse, controllability lets us reach any chosen state at time $1$ from $0$ by an input supported on $[0,1]$. For $t>1$ its output is bounded by $\|u\|_\infty\int_{t-1}^t\|K(s)\|\,ds$, which tends to $0$. Observability then recovers the state from any unit interval of future zero-input output. In detail, $H=\int_0^1 e^{sA^*}C^*Ce^{sA}\,ds$ is positive definite: if its quadratic form vanishes, then $Ce^{sA}v=0$ on $[0,1]$, and differentiation at $0$ gives $CA^jv=0$ for all $j$, hence $v=0$ by the observability rank condition. The formula $x(t)=H^{-1}\int_0^1 e^{sA^*}C^*y(t+s)\,ds$ now gives $x(t)\to0$. Thus every zero-input trajectory decays, so $A$ is Hurwitz.

For the discrete-time converse with $n>0$, reach any state after $n$ steps and then switch the input off. A summable kernel tends to $0$, so convolution with that finite input has output tending to $0$. The full-column-rank observability matrix recovers $x(k)$ from $y(k),\ldots,y(k+n-1)$, giving $x(k)\to0$ and hence convergence of $A$. Dimension $0$ is immediate. The continuous-time real-space reachability and Gramian arguments also cover complex coefficients by writing each complex vector as its real and imaginary parts; this preserves the Euclidean norms and doubles the controllability and observability ranks.

The canonicity hypothesis cannot be dropped. For $A = \operatorname{diag}(1, -1)$, $B = (0, 1)^\top$ and $C = (0, 1)$ the impulse response is $e^{-t}$, which is integrable, but $A$ is not Hurwitz; $(A, B)$ is not controllable. In discrete time, $A = \operatorname{diag}(2, 1/2)$ with the same $B$ and $C$ gives the summable impulse response $2^{-(k-1)}$, while $A$ is not convergent.

## Depends on

- [Minimal realizations are exactly the canonical ones](minimal-realizations-are-canonical.md): canonical realizations are exactly the minimal ones

## Proof depends on

- [Exponential stability of linear differential equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-differential-equations.md): Hurwitz matrices give exponentially decaying $e^{tA}$
- [Exponential stability of linear difference equations](../../ordinary-differential-equations/stability-of-linear-systems/asymptotic-stability-linear-difference-equations.md): convergent matrices give geometrically decaying $A^k$

- [Kalman rank condition](../controllability-of-linear-systems/is-controllable-on-iff-kalman.md): reachability on a positive continuous-time horizon; complex coefficients by the stated realification

- [Reachability of discrete-time linear systems](../controllability-of-linear-systems/kalman-rank-condition-discrete-time.md): reachability after n steps

- [Finite-horizon observability](../observability-of-linear-systems/observability-rank-condition-discrete-time.md): reconstruction from n successive zero-input outputs

- [Observability Gramian](../observability-of-linear-systems/observability-gramian-time-varying.md): the constant-coefficient reconstruction formula on a unit interval

## Sources

- E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., Texts in Applied Mathematics 6, Springer, 1998, <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf>, Section 7.3: Lemma 7.3.1 (uniform BIBO stability if and only if the impulse response is integrable, p. 327), Proposition 7.3.3 (internal stability implies uniform BIBO stability, p. 328), Theorem 33 (canonical and uniformly BIBO stable implies internally stable, p. 329), and Exercise 7.3.7 (a uniformly BIBO stable system that is not internally stable, p. 330).
