# Task claim: the Euler–Lagrange equation

This temporary note opens the draft pull request that claims the ATLAS task
`af_0836382f782000c326c522b6`. It will be removed when the proof lands on this branch.

- Article: `blueprint/roadmap/Analysis/convex-analysis-and-variations/euler-lagrange-equation/euler-lagrange-equation.md`
- Lean declaration: `MathlibExt.Analysis.EulerLagrangeWanted.Analysis.euler_lagrange_equation`, the only theorem of `WantedExt/Analysis/EulerLagrangeWanted.lean`
- Source: L. Euler (1744) and J.-L. Lagrange (1755), as stated in the lean-eval problem `euler_lagrange_equation` (leanprover/lean-eval at 38361be).

Statement to prove, with its name and statement unchanged: if $L(t, y, v)$ is $C^2$, $x$ is $C^2$, and $x$ is a variational extremum of the action
$\int_a^b L(t, x(t), x'(t)) \, dt$ on $(a, b)$, then $\partial L / \partial y = \frac{d}{dt} \, \partial L / \partial v$
along $x$ at every $t \in (a, b)$.
