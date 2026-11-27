# Uniqueness of the exception handler

Let `g : α → β` handle values and `onRaise : E → β` handle exceptions. Every
function `h` on exception computations with `h (pure x) = g x` for every `x`,
and with `h (bind (raise e) k) = onRaise e` for every exception `e` and
continuation `k`, equals the handler `handle g onRaise`.
