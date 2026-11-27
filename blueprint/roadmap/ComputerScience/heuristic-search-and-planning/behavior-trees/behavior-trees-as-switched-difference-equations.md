# Behavior trees as switched difference equations

In the state-space formulation, a **behavior tree** is a triple $T_i = (f_i, r_i, \Delta t)$, where $f_i : \mathbb{R}^n \to \mathbb{R}^n$ defines the difference equation $x_{k+1} = f_i(x_k)$ with time step $t_{k+1} = t_k + \Delta t$, and $r_i : \mathbb{R}^n \to \{R, S, F\}$ returns Running, Success or Failure. The **running**, **success** and **failure regions** $\mathcal{R}_i$, $\mathcal{S}_i$, $\mathcal{F}_i$ are the preimages of $R$, $S$, $F$; they partition the state space. All trees share the state space and the time step. Two trees combine as follows.

- **Sequence.** $T_0 = \mathrm{Sequence}(T_1, T_2)$ has $(r_0, f_0)(x) = (r_2, f_2)(x)$ if $x \in \mathcal{S}_1$, and $(r_0, f_0)(x) = (r_1, f_1)(x)$ otherwise: the second child runs only once the first has succeeded, and the sequence succeeds only when both have.
- **Fallback.** $T_0 = \mathrm{Fallback}(T_1, T_2)$ has $(r_0, f_0)(x) = (r_2, f_2)(x)$ if $x \in \mathcal{F}_1$, and $(r_0, f_0)(x) = (r_1, f_1)(x)$ otherwise: the second child runs only once the first has failed, and the fallback fails only when both have.
- **Parallel.** When the state splits as $x = (x^1, x^2)$ with $T_1$ acting only on $x^1$ and $T_2$ only on $x^2$, $T_0 = \mathrm{Parallel}(T_1, T_2)$ applies both, and returns Success when one child succeeds (threshold $M = 1$) or when both succeed ($M = 2$), Failure when both fail ($M = 1$) or one fails ($M = 2$), and Running otherwise.

Longer compositions are nested: $\mathrm{Sequence}(T_1, T_2, T_3) = \mathrm{Sequence}(T_1, \mathrm{Sequence}(T_2, T_3))$, and likewise for fallbacks. A tree is **finite time successful** with region of attraction $\mathcal{R}' \subseteq \mathcal{R}$ and time bound $\tau$ if from every $x(0) \in \mathcal{R}'$ the state stays in $\mathcal{R}'$ until it enters $\mathcal{S}$ at some time $\tau'(x(0)) \le \tau$.

## Sources

- M. Colledanchise and P. Ögren, *Behavior Trees in Robotics and AI: An Introduction*, CRC Press, 2018, <https://arxiv.org/abs/1709.00084>, Section 5.1: Definition 5.1 (behavior trees as triples $\{f_i, r_i, \Delta t\}$ with running, success and failure regions, p. 63), Definitions 5.2–5.4 (sequence, fallback and parallel compositions, pp. 64–66), and Definition 5.5 (finite time successful, p. 66).
