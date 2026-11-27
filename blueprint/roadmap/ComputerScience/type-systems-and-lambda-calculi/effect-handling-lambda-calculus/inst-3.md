# Instantiating an operation clause

`c.inst₂ x k` is `c[x/1, k/0]`: it replaces the
parameter (index `1`) by `x` and the continuation (index `0`) by `k`, and lowers every other
free variable by two.
