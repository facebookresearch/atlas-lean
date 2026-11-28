# Looking a name up

The closure bound to `x` by the newest binding of `x` in the
environment, or `none` when the environment does not bind `x`. It is `List.lookup x env`, the
value of the first pair in the list whose key is `x`.
