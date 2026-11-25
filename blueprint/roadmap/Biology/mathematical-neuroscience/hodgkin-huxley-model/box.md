# Box of states with voltage in an interval and gating between 0 and 1

For real numbers $V_{lo}$ and $V_{hi}$, the box is the set of states $(V, m, h, n) \in \mathbb{R}^4$
with $V_{lo} \le V \le V_{hi}$ and $m, h, n \in [0, 1]$, that is $[V_{lo}, V_{hi}] \times [0, 1]^3$;
it is empty when $V_{lo} > V_{hi}$. When $[V_{lo}, V_{hi}]$ is a [trapping interval](is-trapping.md)
of [valid parameters](valid.md), solutions that start in the box [stay in it](mem-box.md).
