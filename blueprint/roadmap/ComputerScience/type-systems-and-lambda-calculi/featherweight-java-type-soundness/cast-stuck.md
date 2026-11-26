# Cast Stuck

An expression stuck at a failed cast in evaluation position: a cast `(T) (new K(v̄))` of a
 value for some classes `K` and `T` with `K ≮: T`, under the evaluation contexts of the
 call-by-value `Step` (Lecture #30). The congruence constructors mirror those of `Step` one for
 one. This is the cast-failure case of TOPLAS Theorem 2.4.3, refined from "contains" to "in
 evaluation position".
