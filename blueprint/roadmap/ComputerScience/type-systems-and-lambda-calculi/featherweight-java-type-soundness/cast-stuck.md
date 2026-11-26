# Cast Stuck

An expression stuck at a failed downcast in evaluation position: the cast
 `(D) (new C(v̄))` of a value with `¬ C <: D`, under the evaluation contexts of the
 call-by-value `Step` (Lecture #30). The congruence constructors mirror those of `Step` one for
 one. This is the cast-failure case of TOPLAS Theorem 2.4.3, refined from "contains" to "in
 evaluation position".
