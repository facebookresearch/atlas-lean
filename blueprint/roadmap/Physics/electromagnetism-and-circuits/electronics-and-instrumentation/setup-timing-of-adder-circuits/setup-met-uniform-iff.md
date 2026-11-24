# The certificate is exact under uniform delays

**The certificate is exact under uniform delays**, for a signature whose
operations all take an argument. For a circuit with at least one output,
uniform delay `D ≥ 0` and every input arriving exactly at `tq ≥ 0`, setup holds iff
`tq + D * depth + ts + u ≤ T`. For a signature that also offers constants,
use `setupMet_uniform_iff_of_noConstantGates`.
