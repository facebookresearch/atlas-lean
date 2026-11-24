# Correctness of modified nodal analysis stamping

Assume the [stamping hypotheses](satisfies-stamping-hypotheses.md), and let the node potentials `v`
and the inductor currents `i_L` be differentiable on `ℝ`. For all voltage-source currents `i_V`, the
[stamped equations](satisfies-stamped-equations.md) hold if and only if there are branch voltages
and currents satisfying the [branch equations](satisfies-branch-equations.md) whose restrictions to
the inductor and source branches are `i_L` and `i_V` at every time.
