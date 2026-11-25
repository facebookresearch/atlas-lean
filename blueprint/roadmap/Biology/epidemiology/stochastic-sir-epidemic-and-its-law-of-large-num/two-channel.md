# Two-channel chain

A two-channel chain on a state space `ι`, an arbitrary set, consists of two rate functions
`rate₁, rate₂ : ι → ℝ` and three target maps `target₁, target₂, target₁₂ : ι → ι`. In state `x`,
channel `1` fires at rate `rate₁ x` and moves the chain to `target₁ x`, channel `2` fires at rate
`rate₂ x` and moves it to `target₂ x`, and `target₁₂ x` is the state reached when both channels
fire at the same instant. The definition places no condition on these data: the rates are
arbitrary real functions, and reading them as jump rates presumes the nonnegative rates of a
[valid](is-valid.md) chain.
