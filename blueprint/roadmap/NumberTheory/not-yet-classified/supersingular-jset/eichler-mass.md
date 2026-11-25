# Eichler Mass

The Eichler mass `(p - 1) * ψ(N) / 12` of level `N` in prime characteristic `p`, where `ψ` is
the Dedekind psi function `ArithmeticFunction.dedekindPsi`. For a level `N ≥ 1` not divisible by
`p`, Eichler's mass formula (J. Voight, *Quaternion Algebras*, Theorem 25.3.18 and
Remark 42.3.10) says that the supersingular points of `X₀(N)` over an algebraic closure of
`ZMod p`, each weighted by `2 / |Aut|`, have total mass `eichlerMass N p`; this file does not
prove it. Defined for prime `p` only: prime-power fields `𝔽_q` with `q = p ^ n`, `n > 1`, are out
of scope.
