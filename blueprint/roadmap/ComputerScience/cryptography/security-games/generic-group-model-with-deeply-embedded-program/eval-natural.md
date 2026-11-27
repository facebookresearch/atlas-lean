# Generic-group evaluation is invariant under relabeling

Let `L` and `L'` be label types with decidable equality, with oracles `O1` and
`O2`, and let `phi : L ≃ L'` be a bijection that the oracles respect: `O2 (mul
(phi a, phi b)) = phi (O1 (mul (a, b)))` and `O2 (inv (phi a)) = phi (O1 (inv
a))`. If two environments satisfy `env2 i = phi (env1 i)` for every `i`, then
`eval O2 env2 p = phi (eval O1 env1 p)` for every program `p`.
