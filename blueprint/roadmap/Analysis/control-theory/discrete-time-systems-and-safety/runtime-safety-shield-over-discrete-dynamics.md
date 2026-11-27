# Runtime safety shield (simplex) over discrete dynamics

Let a plant $x' = f(x, u, w)$ have disturbances $w$ in a set $W$, let $S$ be a safe set and let $R \subseteq S$ be a recoverable set:
there is a fallback controller $u_{\mathrm{fb}}$ with $f(x, u_{\mathrm{fb}}(x), w) \in R$ for every $x \in R$ and $w \in W$ (an offline
premise). The shield, at state $x$, applies a proposed control $u$ if $f(x, u, w) \in R$ for every $w \in W$, and applies
$u_{\mathrm{fb}}(x)$ otherwise. Then, from every initial state in $R$, every closed-loop trajectory stays in $R$, hence in $S$,
whatever controls are proposed. The online check is one step; it does not establish the invariance of $R$ under the
fallback, which is assumed.

## Proof

By induction on time. Let $x_k \in R$ and let $u$ be the proposed control. If the shield applies $u$, then
$x_{k+1} = f(x_k, u, w_k) \in R$ by the check, for whichever $w_k \in W$ occurs. Otherwise it applies $u_{\mathrm{fb}}(x_k)$, and
$x_{k+1} = f(x_k, u_{\mathrm{fb}}(x_k), w_k) \in R$ by the premise on the fallback. Since $f$ is total, the step is always
defined, and $R \subseteq S$.

## Depends on

- [Closed-loop composition of plant and controller as discrete dynamics](closed-loop-composition-of-plant-and-controller-as-discrete.md)

## Proof depends on

- [Reachable sets, forward invariants and safety for discrete dynamics](reachable-sets-forward-invariants-and-safety-for-discrete-dy.md)

## Sources

- A. Platzer, *Overview of Logical Foundations of Cyber-Physical Systems*, arXiv:1910.11232, Section 5 (runtime monitors
  used like Simplex monitors, switching to a verified fallback controller). The invariance argument is derived above.
  <https://arxiv.org/pdf/1910.11232>
