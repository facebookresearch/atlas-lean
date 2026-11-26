# Type soundness for the call-by-value `Step`

**Type soundness for the call-by-value `Step`** (TOPLAS Theorem 2.4.3, whose relation is
nondeterministic). In a valid class table, if a closed expression of type `C` reaches a normal
form `e'` by `Steps`, then `e'` is a value typed at some `D <: C`, or `e'` is stuck at a failed
downcast `(D) (new C(v̄))` with `C ≮: D` in evaluation position, which refines TOPLAS's "an
expression containing" such a cast. The proof applies
`Cslib.Languages.TypeSafety.final_or_step_of_reflTransGen` with final states `Value` or
`CastStuck` and the typing predicate "typed at a subtype".
