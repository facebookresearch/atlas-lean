# Stage Weak Eval Naturality Iso

Weak evaluation naturality, degree-generic: evaluating through the weak
inclusion after `mapStageWeak` agrees with mapping after evaluation through
the inclusion. Components reuse the general Stage iso at the underlying stage
object; maps agree by `mapStageWeak_inclusion` (`rfl`) with strict functor
associativity. Orientation matches `stageEvalNaturalityIsoGeneral`:
mapped-then-evaluated on the left, evaluated-then-mapped on the right.
