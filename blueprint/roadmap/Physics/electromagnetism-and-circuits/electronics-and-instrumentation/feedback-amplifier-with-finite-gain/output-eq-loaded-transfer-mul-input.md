# Loaded closed-loop transfer

Any unloaded and loaded output
signals obeying `vamp = A(s) * (a * vi - beta * vo)` and
`vo = b * vamp`, where `a * vi - beta * vo` is the feedback error,
away from both denominator zeros (the open-loop denominator zero, where
`1 + s / wp = 0`, and the loaded denominator zero, where
`1 + s / wp + beta * b * A0 = 0`) and with `wp ≠ 0`, satisfy
`vo = G(s) * vi` for the loaded transfer `G`. The proof clears the
open-loop denominator using `1 + s / wp ≠ 0`, rearranges the two
model equations, and divides by the loaded denominator.
