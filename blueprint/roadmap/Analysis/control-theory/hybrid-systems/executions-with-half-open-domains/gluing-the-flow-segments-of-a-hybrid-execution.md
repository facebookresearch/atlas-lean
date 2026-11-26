# Gluing the flow segments of a hybrid execution

Let $\tau = (I_i)_{i=0}^N$, $N < \infty$, be a hybrid time set with closed intervals $I_i = [\tau_i, \tau'_i]$, at least one of positive length, and let $x_i : I_i \to \mathbb{R}^n$ be continuously differentiable with $\dot x_i(t) = f_i(x_i(t))$ on $I_i$ for continuous vector fields $f_i$, such that consecutive segments match, $x_{i+1}(\tau_{i+1}) = x_i(\tau'_i)$ (identity resets). Define $z : [\tau_0, \tau'_N] \to \mathbb{R}^n$ by $z(t) = x_i(t)$ for $t \in I_i$ with $\tau_i < \tau'_i$, and let $\sigma(t)$ be the index of the last interval of positive length containing $t$. Then:

1. **Well defined.** $z$ is well defined and continuous; segments of length zero do not affect it.
2. **Durations.** The total elapsed time is $\tau'_N - \tau_0 = \sum_{i=0}^N (\tau'_i - \tau_i)$, and the intervals of positive length cover $[\tau_0, \tau'_N]$ with overlaps only at their endpoints.
3. **Integral equation.** $z(t) = z(\tau_0) + \int_{\tau_0}^t f_{\sigma(s)}(z(s))\, ds$ for all $t$, so $z$ is Lipschitz and differentiable with $\dot z(t) = f_{\sigma(t)}(z(t))$ at every $t \in (\tau_0, \tau'_N)$ that is not a switching time $\tau'_i$. At a switching time $\tau'_i < \tau'_N$ that ends a positive-length segment $i$, $z$ has left derivative $f_i(x_i(\tau'_i))$ and right derivative $f_j(x_j(\tau_j))$, where $j > i$ is the next index with $\tau_j < \tau'_j$; such a $j$ exists because $\tau'_i < \tau'_N$.

If every interval has length zero, the time domain is the single instant $\tau_0$ and the execution consists of instantaneous transitions only; that case is excluded above. No derivative is asserted at switching times: $z$ is differentiable there only when the one-sided derivatives agree, for example when the two vector fields agree at the switching point.

**Proof.** At a shared endpoint $\tau'_i = \tau_{i+1}$ the definitions agree by the matching condition; through a run of zero-length intervals the matching condition passes the same value along, so the next positive-length segment starts where the previous one ended. Part 2 is the telescoping sum $\sum_i (\tau'_i - \tau_i) = \tau'_N - \tau_0$, using $\tau'_i = \tau_{i+1}$. For part 3, on each positive-length interval the fundamental theorem of calculus gives $x_i(t) = x_i(\tau_i) + \int_{\tau_i}^t f_i(x_i)$, and summing over the intervals before $t$ with the matching condition gives the integral equation; the integrand is bounded on the compact interval, so $z$ is Lipschitz.

## Background

- [Gluing solutions of an ODE](../../../ordinary-differential-equations/maximal-solutions-and-global-existence/has-deriv-at-piecewise-union-of-eq-on.md): gluing two solutions of one differential equation on overlapping open sets
- [Executions of a hybrid automaton](executions-of-a-hybrid-automaton.md): hybrid time sets and their segments

## Sources

- J. Lygeros, *Lecture Notes on Hybrid Systems*, ENSIETA, 2004, <https://people.eecs.berkeley.edu/~sastry/ee291e/lygeros.pdf>, Definition 3.2 (hybrid time sets, with $\tau'_i = \tau_{i+1}$ and zero-length intervals for simultaneous transitions, pp. 23–24) and Definition 3.3 (hybrid trajectories, p. 25). The gluing statement is proved on the page.
