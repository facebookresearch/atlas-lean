# Continuations

What remains to be done with the value being computed, in one of three
forms. The empty continuation `mt` means that the value is the result. The argument frame
`ar site arg env k` holds the argument `arg` of the application labelled `site`, the environment
`env` in which to evaluate it, and the continuation `k` that follows. The function frame
`fn site f k` holds the function closure `f` of the application labelled `site` and the
continuation `k` that follows. The label `site` records the application a frame belongs to; no
transition rule inspects it.
