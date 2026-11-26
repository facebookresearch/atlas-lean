# Instantiating a computation

`c.inst v` is `c[v/x]` for the innermost variable `x`:
it replaces index `0` of `c` by `v` and lowers every other free variable by one.
