# Answers

A computation is an answer when it returns a value, or when it is an operation
call `op o v` in an evaluation context none of whose handlers handles `o`. Handler frames are
handler literals, so a call under `with h handle …` with `h` a variable or any other non-handler
value is not an answer. This is Hillerström-Lindley 2016, Definition 3.2, without the condition
that the operation lies in an effect set, so the predicate does not depend on types.
