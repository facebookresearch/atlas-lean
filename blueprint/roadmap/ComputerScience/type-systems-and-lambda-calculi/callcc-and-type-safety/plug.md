# Plugging an evaluation context

`E.plug t` fills the hole of `E` with the term `t`: the
empty context gives `t`, and a context whose innermost frame is `F` plugs the rest of the
context with `F` filled by `t`.
