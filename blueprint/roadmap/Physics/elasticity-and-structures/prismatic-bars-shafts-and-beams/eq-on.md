# Uniqueness for the fixed-fixed problem

Let $k > 0$, let $L$ be real and $f \colon \mathbb{R} \to \mathbb{R}$. If $u$ and $v$ both solve the
[fixed-fixed problem](is-fixed-fixed-solution.md) on $[0, L]$ with rigidity $k$ and load $f$, then
$u(x) = v(x)$ for every $x \in [0, L]$. No condition on $L$ or $f$ is needed: for $L < 0$ the
interval is empty and for $L = 0$ both functions vanish at $0$. Outside $[0, L]$ the two functions
can differ.

Proof: for $L > 0$, rescale to $[0, 1]$ ([rescaling](is-fixed-fixed-solution-scale.md)) and apply
[uniqueness for the Sturm–Liouville Dirichlet problem](../../../Analysis/ordinary-differential-equations/sturm-liouville-dirichlet-problem/sturm-liouville-uniqueness.md)
with zero potential.
