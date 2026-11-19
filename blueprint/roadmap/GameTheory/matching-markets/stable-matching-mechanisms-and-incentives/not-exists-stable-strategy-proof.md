# Roth's impossibility theorem

No stable matching mechanism makes truthful revelation a dominant strategy for all agents. Precisely, for
the markets with three men and three women, there is no matching mechanism $h$ such that $h(P)$ is stable
for every stated profile $P$ and, for every man and every woman, no misreport ever yields a partner
preferred under the agent's true preference.

This is exactly Roth's Theorem 3, which Roth also proves by exhibiting one market: the theorem asserts that
*some* market defeats every stable mechanism, not that every mechanism is manipulable at every profile. The
proof is the one of the source: at Roth's profile, any stable mechanism gives either man $m_1$ or woman
$w_1$ a profitable misreport.

The impossibility rests on stability: a constant mechanism is strategy-proof, and Roth's Theorem 4 (serial
dictatorship) gives Pareto-efficient strategy-proof mechanisms.

## Informally uses

- [In Roth's market every stable mechanism is manipulable](roth-stable-mechanism-manipulable.md): the manipulation at Roth's profile, from which the theorem follows at once.

## Background

- [Gibbard–Satterthwaite theorem](../../social-choice/gibbard-satterthwaite-theorem/README.md): Roth compares his result to the impossibility theorems of Gibbard and Satterthwaite for social choice functions (Roth 1982, §1).
- [Gale–Shapley theorem](../../../GraphTheory/matchings-and-flows/stable-marriage-problem/gale-shapley-exists-stable-matching.md): stable mechanisms exist, so the theorem is not vacuous.
- [Strategy-proofness of the man-optimal stable mechanism for the men](man-optimal-mechanism-strategy-proof-for-men.md): the positive counterpart, where incentives to misreport are confined to one side.

## Sources

- A. E. Roth, "The economics of matching: stability and incentives", *Mathematics of Operations Research* 7(4) (1982), 617–628, Theorem 3 and its proof.
