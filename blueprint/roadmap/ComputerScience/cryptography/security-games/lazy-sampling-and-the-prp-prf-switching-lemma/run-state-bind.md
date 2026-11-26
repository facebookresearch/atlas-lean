# Stateful oracle execution turns binding into PMF bind

For a stateful probabilistic oracle `O : σ → X → PMF (Y × σ)`, an oracle
computation `c` and a continuation `g`, running `c` followed by `g` from state
`s` equals running `c` from `s` and then, for its result `a` and final state
`s'`, running `g a` from `s'`; that is, `runState O (bind c g) s = (runState O
c s).bind (fun p => runState O (g p.1) p.2)`.
