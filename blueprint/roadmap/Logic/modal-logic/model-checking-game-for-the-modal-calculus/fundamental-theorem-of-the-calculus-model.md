# Fundamental theorem of the μ-calculus model-checking game

Let $M$ be a Kripke model, $\mathit{env}$ an environment, $\varphi$ a closed formula of the modal $\mu$-calculus and $w$ a world. In the model-checking
game, positions consist of a subformula, a world and a binder stack. Verifier moves at disjunctions and diamonds, Refuter at
conjunctions and boxes, and fixpoint binders and their variables are unfolded. A position $(\mu X.\psi, w, s)$ with $k$ binders on the stack
$s$ has priority $2k + 1$, a position $(\nu X.\psi, w, s)$ has priority $2k + 2$, and an infinite play is won by Verifier exactly when the least
priority occurring infinitely often is even. Then Verifier has a winning strategy from $(\varphi, w, [\,])$ if and only if $w$ satisfies $\varphi$ in $M$
under $\mathit{env}$.

The priority assignment refines the alternation-depth priorities, so outer binders dominate. For example, in the one-world reflexive
model, $\mu X.\, \nu Y.\, X$ is false and Verifier loses its only infinite play, whose least recurring priority is $1$.

For the variant of the game that unfolds a fixpoint by substitution, assigns $\mu X.\psi$ the priority $2\,\mathrm{nd}(\mu X.\psi) + 1$ and $\nu X.\psi$ the
priority $2\,\mathrm{nd}(\nu X.\psi)$, where $\mathrm{nd}$ is the fixpoint nesting depth, and lets the largest recurring priority decide, the theorem holds
for arbitrary, possibly infinite, transition systems. Satisfaction implies a win for Verifier by induction on the formula, and the
converse follows by dualizing the formula and using determinacy.

## Depends on

- [Formulas of the modal μ-calculus](../modal-calculus/mu-formula.md)
- [Position of the μ-calculus model-checking game](game-position.md)
- [Priority of a game position](prio.md)
- [Parity winning condition](parity-win.md)
- [Verifier has a winning strategy](verifier-wins.md)
- [Satisfaction in the modal μ-calculus](../modal-calculus/sat.md)

## Expansion

This page becomes ready once these prerequisites are stated:

- Positional determinacy of parity games with finitely many priorities: every position is won by exactly one player, by a positional
  strategy (proof prerequisite).
- Correspondence between the binder-stack game with least-priority parity used here and the substitution game with nesting-depth
  priorities and largest-priority parity (proof prerequisite).

## Sources

- M. Hofmann and H. Rueß, "Certification for μ-calculus with winning strategies", arXiv:1401.1693: Section 3 (parity games, Theorem 1 on positional determinacy), Section 3.2 (the model-checking game, its priorities, Theorem 2 and Corollary 1) and Lemmas 1–2.
