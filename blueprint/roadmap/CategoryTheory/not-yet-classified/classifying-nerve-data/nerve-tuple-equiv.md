# Nerve Tuple Equiv

Degreewise nerve tuple equivalence.

Reads consecutive arrows with `unop`; rebuilds with `mkOfObjOfMapSucc` from
segment data `op (t i)`. `t 0` is the first nerve arrow, matching the
outermost tensor factor. The reader lives in the lightweight
`MathlibExt.CategoryTheory.NerveSingleObj` module.
