# Explicit Bernoulli anytime-valid confidence sequence, self-contained

For fixed
reference `p0 ∈ (0,1)`, every interior null `θ` with iid Bernoulli(`θ.val`) data carries
coverage `≥ 1 - α` through the inverted family. The family e-process property is derived
internally by exact application of `bernoulli_null_lr_eProcess`, then composed through
the sibling `anytime_coverage_of_eProcess` on the interior subtype (no `hE`/`hville`
premises, no duplicated Ville/inversion machinery). The conclusion is a confidence
sequence over the interior subtype, not a claimed real-line interval.
