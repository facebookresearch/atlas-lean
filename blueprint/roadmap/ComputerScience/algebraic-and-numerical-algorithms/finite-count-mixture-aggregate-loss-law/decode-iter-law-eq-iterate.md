# Decode iter Law eq iterate

Decoding the deterministic-count law `iterLaw S n` gives the `n`-fold independent sum of `decode S` draws: iterating `q ↦ q.bind (fun a => (decode S).map (a + ·))` `n` times from `PMF.pure 0`.
