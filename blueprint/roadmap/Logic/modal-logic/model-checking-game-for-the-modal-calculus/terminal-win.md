# Winner at a terminal position

Let $M$ be a Kripke model and $\mathit{env}$ an environment
assigning a predicate on worlds to every index. At a game position $(\varphi, w, st)$, where $st$
is the stack of enclosing fixpoint binders and $|st|$ its length, Verifier wins exactly when
$\varphi$ is an atom $a$ true at $w$, a negated atom $\neg a$ with $a$ false at $w$, $\top$, a
box $\Box\psi$, or a variable with de Bruijn index $n \ge |st|$ such that
$\mathit{env}(n - |st|)$ holds at $w$. At every other position (a variable with index
$n < |st|$, $\bot$, a diamond, a conjunction, a disjunction or a fixpoint) Refuter wins.

The condition is consulted only at positions with no moves: a box with no successors leaves
Refuter stuck and a diamond with no successors leaves Verifier stuck, while a bound variable,
a conjunction, a disjunction and a fixpoint always have a move. The environment index is
shifted by $|st|$ because each binder on the stack shifts de Bruijn indices by one.

## Sources

- C. Stirling, *Modal and Temporal Properties of Processes*, Springer 2001, Chapter 6.
