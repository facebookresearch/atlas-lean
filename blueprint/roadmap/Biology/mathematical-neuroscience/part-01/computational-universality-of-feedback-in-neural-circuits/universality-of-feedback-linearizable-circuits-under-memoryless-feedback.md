# Universality of feedback-linearizable circuits under memoryless feedback

**Setting.** Consider a fixed $n$-dimensional circuit with one feedback input $v$,

$$x'(t) = f(x(t)) + g(x(t))\, v(t), \qquad x(t) \in \mathbb{R}^n, \tag{A}$$

with smooth vector fields $f, g$, and an arbitrary $n$-th order input-driven system to be emulated,

$$z^{(n)}(t) = G\big(z(t), z'(t), \dots, z^{(n-1)}(t)\big) + u(t), \tag{B}$$

with $G : \mathbb{R}^n \to \mathbb{R}$ smooth. Two systems $x' = f(x) + g(x)v$ and $\tilde x' = \tilde f(\tilde x) + \tilde g(\tilde x) v$ are **feedback equivalent** if there are a diffeomorphism $T$ of $\mathbb{R}^n$ and smooth $\alpha, \beta : \mathbb{R}^n \to \mathbb{R}$ with $\beta \ne 0$ everywhere such that $T_*(x)\big(f(x) + g(x)\alpha(x)\big) = \tilde f(T(x))$ and $T_*(x)\, g(x)\beta(x) = \tilde g(T(x))$. Let $S_n$ be the class of systems (A) that are globally **feedback linearizable**, i.e. feedback equivalent to a controllable linear system; equivalently, feedback equivalent to the integrator chain $x_1' = x_2, \dots, x_{n-1}' = x_n, x_n' = v$.

**Theorem.** If (A) belongs to $S_n$, then for every system (B) there are a smooth memoryless feedback $K : \mathbb{R}^n \times \mathbb{R} \to \mathbb{R}$ and a smooth memoryless readout $h : \mathbb{R}^n \to \mathbb{R}$, depending only on $G$, such that for every input $u$ and every solution $z$ of (B) there is an auxiliary input $u_0$ with $u_0(t) = 0$ for $t \ge 1$ for which the solution of

$$x' = f(x) + g(x)\, K\big(x, u(t) + u_0(t)\big), \qquad x(0) = 0,$$

satisfies $h(x(t)) = z(t)$ for all $t \ge 1$. Moreover, for every $c > 0$ there is $C > 0$ such that if $|u(t)| \le c$ and $|z^{(i)}(t)| \le c$ for $i < n$ and all $t$, then $|K(x(t), u(t) + u_0(t))| \le C$, so a bounded saturating nonlinearity (for example $q\tanh$) can be applied to the feedback without loss. Systems of $k$ coupled higher-order equations are emulated in the same way with $k$ memoryless feedbacks.

Consequently a circuit in $S_n$ that has fading memory on its own acquires, through a trained static feedback and readout, the dynamic response of any system (B), including persistent-memory and (via known embeddings) Turing-universal computation.

## Expansion

By the characterization of $S_n$ there are $T, \alpha, \beta$ such that, for any input $\mu$ and any solution $Z = (z, z', \dots, z^{(n-1)})$ of the chain $z^{(n)} = \mu$, the curve $x = T^{-1}(Z)$ solves (A) with $v = \alpha(x) + \beta(x)\mu$. Take $h(x) = T_1(x)$ (first coordinate) and

$$K(x, w) = \alpha(x) + \beta(x)\big(G(T(x)) + w\big),$$

so that $\mu = G(Z) + u + u_0$ reproduces (B). The input $u_0$, supported in $[0, 1]$, steers the chain from $Z(0) = T(0)$ to the required state $Z(1)$ of the target solution, using controllability of the chain; this lets a standardized initial condition emulate arbitrary initial conditions. Boundedness follows from continuity of $T^{-1}$, $\alpha$, $\beta$ and $G$ on bounded sets. The source complements this with a noise-robust result (its Theorem 2, made precise as Theorem 5): fading-memory filters with bounded additive noise and imperfect feedback can emulate any finite state machine, because the feedback can be chosen to cancel the effect of earlier feedback errors; noise rules out simulating arbitrary Turing machines but not finite state machines.

## Sources

- W. Maass, P. Joshi, E. D. Sontag, "Computational aspects of feedback in neural circuits", PLoS Computational Biology 3 (2007), e165, Theoretical Analysis (Theorem 1, Theorem 2) and Methods ("Definition of feedback equivalence", "Definition of the class $S_n$" with its Lemma, "Details to the proof of Theorem 1", Corollary 3, Theorem 5), <https://doi.org/10.1371/journal.pcbi.0020165> (PMC1779299).
- E. D. Sontag, *Mathematical Control Theory*, 2nd ed., Springer (1998), Definition 5.3.1 and Lemma 5.3.5 (feedback equivalence and linearizability).
