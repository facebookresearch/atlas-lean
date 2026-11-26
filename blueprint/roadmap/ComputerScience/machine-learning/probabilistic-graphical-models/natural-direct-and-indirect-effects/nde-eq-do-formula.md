# Experimental identification of the NDE

**P14, Theorem 1, eq. (13)** (P01, Theorem 1, experimental identification). Let `X` (node `t`) and
`Z` (node `m`) be nodes of a finite recursive structural causal model with values in a finite set
and independent noise laws, `Y` an outcome node read through a real function `g`, `x`, `x*` two
treatment values, and `W` a set of nodes inside a set `S` of nodes that contains the parents of each
of its members and contains neither `t` nor `m`: no member of `W` is a descendant of the treatment
or of the mediator, a premise stronger than P14's A-1, which excludes only descendants of the
treatment. Assume the cross-world independence `Y_{x'z} ⫫ Z_{x*} | W` under the noise law, for `x'`
in `{x, x*}` and every mediator value `z` (P01, eq. (7)). Then

`NDE(x, x*; Y) = ∑_{w,z} [E(g(Y) | do(x, z), w) - E(g(Y) | do(x*, z), w)] P(Z = z | do(x*), w) P(w)`,

where `E(g(Y) | do(x, z), w)` is the mean given `W = w` under the law of `do(X = x, Z = z)`,
`P(Z = z | do(x*), w)` the probability given `W = w` under the law of `do(X = x*)`, and `P(w)` the
observational probability of `W = w`: every factor is an interventional or the observational law.
The terms with `P(w) = 0` vanish; in the others every conditioning event has positive probability,
since interventions on the treatment and the mediator leave the law of `W` unchanged.
