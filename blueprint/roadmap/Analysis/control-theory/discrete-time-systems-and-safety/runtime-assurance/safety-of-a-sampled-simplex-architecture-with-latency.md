# Safety of a sampled simplex architecture with latency

Consider a plant whose state $x(t) \in \mathbb{R}^n$ evolves in continuous time under either a primary or a backup controller, a safe set $\mathrm{Safe}$, and a set $R \subseteq \mathrm{Safe}$. Assume:

1. **robust backup invariance:** every trajectory under the backup controller that starts in $R$ stays in $R$ for all later times, for every admissible disturbance;
2. **sound lookahead:** at each decision time $t_k$ the monitor computes, from an estimate $\hat x_k$ with $|x(t_k) - \hat x_k| \le \varepsilon$, a set $Q_k$ containing every state reachable in time $[0, \delta]$ from any state within $\varepsilon$ of $\hat x_k$ under the primary controller and every admissible disturbance;
3. **timing:** the decision times $t_0 < t_1 < \cdots$ satisfy $t_k \to \infty$ as $k \to \infty$, consecutive decision times satisfy $t_{k+1} - t_k \le h_{\max}$, a switch decided at $t_k$ takes effect within $\ell_{\max}$, and $\delta \ge h_{\max} + \ell_{\max}$;
4. **decision rule:** the primary controller is kept at $t_k$ only if $Q_k \subseteq R$; otherwise the backup controller is engaged and kept for all later times (latched switching).

If the primary controller is kept at the first decision time $t_0$, or the backup controller is already in effect at $t_0$ with $x(t_0) \in R$, then $x(t) \in \mathrm{Safe}$ for all $t \ge t_0$.

**Proof.** Because $t_k \to \infty$, the intervals $[t_k, t_{k+1}]$ cover $[t_0, \infty)$. While the primary controller is kept, suppose it was kept at $t_k$, so $Q_k \subseteq R$. Until the next decision takes effect, at most $h_{\max} + \ell_{\max} \le \delta$ after $t_k$, the primary controller drives the state from $x(t_k)$, which is within $\varepsilon$ of $\hat x_k$, so by soundness the state stays in $Q_k \subseteq R$. If the decision at $t_{k+1}$ keeps the primary controller, the argument repeats. If it engages the backup, the switch takes effect at a time $s \le t_{k+1} + \ell_{\max} \le t_k + \delta$, when the state is still in $Q_k \subseteq R$; from then on robust backup invariance keeps it in $R$. In every case the state stays in $R \subseteq \mathrm{Safe}$.

## Proof depends on

- [Runtime safety shield (simplex) over discrete dynamics](../runtime-safety-shield-over-discrete-dynamics.md): the discrete-time form of the same invariance argument
- [A sampled safety margin with bounded drift certifies safety over a latency window](a-sampled-safety-margin-with-bounded-drift-certifies-safety-over-a-latency-window.md): the margin form of the lookahead test over the latency window

## Sources

- K. L. Hobbs, M. L. Mote, M. C. L. Abate, S. D. Coogan and E. M. Feron, "Runtime assurance for safety-critical systems: an introduction to safety filtering approaches for complex control systems", *IEEE Control Systems Magazine* 43(2), 2023, <https://arxiv.org/abs/2110.03506>, "The Simplex Architecture" (plant, primary controller, backup controller, boundary monitor and decision logic, pp. 27–28), latched implementations (pp. 20–21), and the implicit simplex filter, which uses an overapproximation of the reachable set and a robustly forward invariant backup set in the nondeterministic case (pp. 34–35). The continuous-time composition with sampling and latency is proved on the page.
