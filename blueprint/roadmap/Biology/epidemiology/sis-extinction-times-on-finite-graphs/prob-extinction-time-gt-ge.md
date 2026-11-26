# Slow die-out

**Slow die-out** (Ganesh, Massoulié and Towsley 2005, Theorem 4.1, Eq. (6), with the error
term made explicit). Let `G` be a finite connected graph on `n` vertices, let `2 ≤ m ≤ n / 2`,
let `β > 0` with `β η(G, m) > 1`, and put `r = 1 / (β η(G, m))`. Run the SIS process with
infection rate `β` and recovery rate `1` from any nonempty set `X₀` (`hQ` records that its rate
matrix is a rate matrix). Then the extinction time `τ` satisfies
`P(τ > ⌊(β η(G, m))^(m-1)⌋ / (2m)) ≥ ((1 - r) / e) (1 - K r^m)`, where
`K = sup_{x ≥ 1} x² (e^(1/2) / 2)^(x-1)` (`dieOutConstant`).

## Sources

- A. Ganesh, L. Massoulié and D. Towsley, "The effect of network topology on the spread of epidemics", in *Proceedings of IEEE INFOCOM 2005*, vol. 2, pp. 1455–1466, Theorem 4.1, doi:10.1109/INFCOM.2005.1498374.
