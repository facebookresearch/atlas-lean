# Uncoupled dynamics do not lead to Nash equilibrium

Let $0 < \varepsilon < 1$ and consider Jordan's three-player two-action games with parameters
$a_i \in (1 - \varepsilon, 1 + \varepsilon)$ and dynamics $\dot x = F(x; a)$ on the probabilities of the players' first
actions. No dynamic is both uncoupled (each $F_i$ depends on the game only through player $i$'s
own payoffs, here $a_i$) and, for every game of the family, $C^1$ with the Nash equilibrium
(unique for these parameters) as a rest point whose Jacobian has only eigenvalues of negative
real part.

Hart and Mas-Colell's Theorem 1 says that no uncoupled dynamic is Nash-convergent on a
neighbourhood of Jordan's game; Nash-convergent dynamics have the properties above by their
standing regularity assumptions (§I). The statement here is stronger than Theorem 1 as worded:
it drops trajectory convergence and asks for uncoupledness only on Jordan's family. It is exactly
what the §III argument proves: $F^1(y^1, \tfrac12, \tfrac12) = 0$ for the games with
$a_3 = y^1/(1 - y^1)$ forces $\partial F^1/\partial x^1 = 0$ at the equilibrium, and likewise
for the other players, so the Jacobian has trace $0$, which contradicts stability (Hart and
Mas-Colell note that $\det J \neq 0$ already suffices, footnote 15). Uncoupled
dynamics can, by contrast, reach the set of correlated equilibria
([regret matching](regret-matching-tendsto-correlated-eq.md)).

## Sources

- S. Hart and A. Mas-Colell, "Uncoupled dynamics do not lead to Nash equilibrium", Amer. Econ. Rev. 93(5) (2003), 1830–1836, §I, Theorem 1, §III and footnote 15.
- S. Hart, "Adaptive heuristics", Econometrica 73(5) (2005), 1401–1430, §8, Theorem 3.
