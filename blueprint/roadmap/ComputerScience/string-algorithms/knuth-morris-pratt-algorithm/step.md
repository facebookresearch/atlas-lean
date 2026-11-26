# Transition function of the KMP matcher

Suppose an input `xs` has a suffix matching the pattern prefix `t.pattern[:len]`, where `len : Fin (t.size + 1)`. Then `xs.push x` has a suffix matching the pattern prefix `t.pattern[:t.step x len]`, and if `len` is as large as possible then so is `t.step x len`.
