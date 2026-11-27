# Law of a loss on a finite sample space

For a loss `X` on a finite sample space with weights `p(ω)` (in use, nonnegative and summing
to `1`), the loss law is the measure `∑_ω p(ω) δ_{X(ω)}` on the real line, which puts mass
`p(ω)` at `X(ω)`. It is defined for all real weights: each weight is clamped to `max(p(ω), 0)`,
so a negative weight puts no mass at its outcome.
