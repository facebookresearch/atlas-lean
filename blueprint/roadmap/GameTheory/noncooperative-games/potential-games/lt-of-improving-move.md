# Improving moves decrease the potential

If $\Phi$ is an exact potential and $t$ is reached from $s$ by an improving move, then
$\Phi(t) < \Phi(s)$.

The same holds for a strict better-response step from $s$ to $s'$ in a game with finitely many players and finite nonempty strategy sets: $\Phi(s') < \Phi(s)$ (`strict_better_response_decreases_potential`, and `IsStrictBetterResponse.potential_lt` with the step bundled). The exact-potential predicate there asserts the same cost-difference equality with the player and profile quantifiers interchanged; the result here needs no finiteness assumption.
