# Values

Variables (de Bruijn indices), the unit value, the booleans, functions
`fun x ↦ c` whose body binds index `0`, and handlers
`handler {return x ↦ c_r, o₁(x; k) ↦ c₁, …}` given by a return clause binding index `0` and a
list of operation clauses, each binding the parameter `x` at index `1` and the continuation `k`
at index `0` (Pretnar 2015, Fig. 1).
