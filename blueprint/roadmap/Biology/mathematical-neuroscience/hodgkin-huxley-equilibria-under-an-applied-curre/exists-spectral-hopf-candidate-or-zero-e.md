# A spectral Hopf candidate or a zero eigenvalue on the equilibrium branch

There is a
branch voltage `V* ∈ (0, 15)` mV, with applied current `I* = I∞(V*)` and equilibrium `eqPoint V*`
of the squid system with current `I*`, such that either

* the Jacobian there satisfies the spectral Hopf conditions `IsSpectralHopfCandidate ω` (a simple
  pair `± i ω`, `ω > 0`, and every other eigenvalue in the open left half-plane), and for every
  `W ∈ [0, V*)` the branch equilibrium with current `I∞(W)` has a Hurwitz Jacobian, so `V*` is
  the first branch voltage in `[0, 15]` where the Jacobian stops being Hurwitz; or
* `0` is an eigenvalue of the Jacobian at `eqPoint V*`, i.e. `I∞'(V*) = 0`
  (`zero_mem_spectrum_jac_iff`); this alternative says nothing about the branch below `V*`.

Neither transversality nor fold nondegeneracy is shown. `exists_spectral_hopf_candidate` shows
that the first alternative holds.
