# Barrier certificates for discrete-time systems

This node collects barrier certificates for discrete systems and the conditions needed for hybrid systems.

## Expansion

A sound expansion has separate pages for:

1. **Discrete barrier theorem.** For a discrete system $(X, W, f)$ with initial set $I$ and unsafe set $B$, a function
   $V : X \to \mathbb{R}$ with $V \le 0$ on $I$, $V > 0$ on $B$, and $V(x) \le 0 \Rightarrow V(f(x, w)) \le 0$ for every disturbance $w$, certifies
   that no trajectory from $I$ reaches $B$; in particular the decrease condition $V(f(x, w)) \le V(x)$ for all $x$ and $w$
   implies this sublevel condition and gives the same conclusion.
2. **Hybrid extension.** Per-location functions $V_\ell$ with the initial and unsafe conditions, a jump condition
   ($V_{\ell'}(r(x)) \le 0$ whenever $V_\ell(x) \le 0$, the guard holds and $r$ is the reset), and a continuous-flow condition that
   keeps $\{V_\ell \le 0\}$ invariant along the flow within the location invariant; the jump condition alone does not prove hybrid
   safety.
3. **Continuous-time barrier rule,** a separate node. Prajna and Jadbabaie's Theorem 1 imposes the derivative condition only
   on the zero level set $\{B = 0\}$, which does not suffice: for $\dot x = 1$ on $\mathbb{R}$ with $B(x) = x^3$, initial set
   $\{x \le -1\}$ and unsafe set $\{x \ge 1\}$, all three conditions hold, yet the trajectory from $-1$ reaches $1$ at time $2$. The
   flow condition (7) of their hybrid Theorem 2 has the same defect, which is why item 2 states the flow condition as
   invariance of $\{V_\ell \le 0\}$.

## Depends on

- [Reachable sets, forward invariants and safety for discrete dynamics](../discrete-time-systems-and-safety/reachable-sets-forward-invariants-and-safety-for-discrete-dy.md)

## Sources

- Safety Verification of Hybrid Systems Using Barrier Certificates — S. Prajna, A. Jadbabaie, HSCC 2004. <https://web.mit.edu/~jadbabai/www/papers/hscc04_2.pdf> Theorem 1 (conditions (2)–(4)) and Theorem 2 (hybrid conditions (5)–(8), with the jump condition (8)).
