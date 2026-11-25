# Action model logic

This node covers action models and the logic of epistemic actions of Baltag, Moss and Solecki, which
generalize public announcements. An action model is a relational structure with a finite set of events, an
accessibility relation for each agent and a precondition formula for each event. The product update of
a Kripke model $M$ with an action model $A$ has as worlds the pairs $(v, f)$ of a world and an event
whose precondition holds at $v$, an $a$-arrow from $(v_1, f_1)$ to $(v_2, f_2)$ exactly when
$v_1 \mathrel{R_a} v_2$ in $M$ and $f_1 \mathrel{R_a} f_2$ in $A$, and the valuation inherited from $M$.
The formula $[A, e]F$ holds at $w$ when, if the precondition of $e$ holds at $w$, then $F$ holds at
$(w, e)$ in the product update. Without common knowledge, reduction axioms make every formula of the
logic of epistemic actions provably equivalent to an action-model-free modal formula, which yields
soundness and completeness over any action-friendly modal logic.

## Expansion

A sound expansion fixes the syntax with action-model modalities, product update and the closure of
classes of Kripke models under product update (reflexive, transitive and Euclidean relations are
preserved under the stated conditions), and then has separate pages for: the reduction axioms and the
reduction theorem without common knowledge; soundness and completeness for action-friendly logics;
and the extension with common knowledge, which needs its own source. A public announcement is the
special case of a single event, related to itself for every agent, whose precondition is the announced
formula.

## Sources

- A. Baltag and B. Renne, *Dynamic epistemic logic*, Stanford Encyclopedia of Philosophy, first
  published 24 June 2016, §3.1–§3.3. <https://plato.stanford.edu/entries/dynamic-epistemic/>
