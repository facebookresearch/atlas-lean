# Positive critical Hausdorff gauge measure of chordal SLE segments

Fix $0<\kappa<8$, write $d=1+\kappa/8$, and take a probability law with a measurable-at-each-time ordinary chordal $\mathrm{SLE}_\kappa$ trace $\gamma$ in the closed upper half-plane. In the capacity-two convention, almost surely the trace is continuous from $0$, and on the unbounded component of the upper half-plane minus the past trace there are inverse holomorphic conformal maps $g_t,f_t$ to and from the upper half-plane. One has $g_0(z)=z$, $\partial_tg_t(z)=2/(g_t(z)-\sqrt\kappa B_t)$ for surviving points, with derivative taken within nonnegative times, and $z(g_t(z)-z)\to2t$ towards infinity within that component. The tip is the limit of $f_t(\sqrt\kappa B_t+iy)$ as $y\downarrow0$, for a real Brownian motion $B$ under the same probability law.

Let $h$ be continuous and nondecreasing on $[0,\infty)$, with $h(0)=0$ and $h(r)>0$ for $r>0$. Assume $h(r)=r^d(\log\log(1/r))^{(2-d)/2}$ for all sufficiently small positive $r$. Then, almost surely, $\mathcal H^h(\gamma([s,t]))>0$ simultaneously for all real $0<s<t<\infty$. No finiteness or matching upper estimate is asserted.

**Conventions.** Use the trace-driven Loewner description above and the Hausdorff outer measure from costs $h(\operatorname{diam}U)$ for arbitrarily fine covers. The source extends the costs to finite nonnegative radii through the real gauge.

## Depends on

- [Capacity-two chordal Loewner trace and Hausdorff gauge](capacity-two-sle-trace.md)

## Expansion

A local positive-gauge estimate for the Brownian-driven trace, a restart argument in surviving domains back to the half-plane, and a countable-to-simultaneous segment argument.

Identify the native Brownian and Loewner models, prove the small-radius gauge comparison under the conformal maps at restart, and reduce arbitrary positive intervals to embedded rational-time intervals by monotonicity of Hausdorff measure. Keep the event almost sure before quantifying over all intervals.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SLELowerPositivity.lean#L78-L80)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/230.md)
- [Accompanying manuscript: An explicit exact Hausdorff gauge for SLE: A regular formula from quantitative tails and dense visits](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026/An-explicit-exact-Hausdorff-gauge-for-SLE-September-26-2026.pdf)
