# Memoryless pair HMM

The pair HMM's transition weights do not depend on the current state: every transition into
an emitting state `s` (from the begin state or from any emitting state) has weight `π s`, and
every transition into the end state has weight `τ`.
