# Atomic boxes in the translated model

For an atomic program $a$, the formula $[a]\varphi$ holds at a world $w$ of a PDL model if and only if every $a$-successor of $w$, in the labelled transition system underlying the model, satisfies $\varphi$ in the original PDL model. The body $\varphi$ is a PDL formula and may itself contain boxes over compound programs; the statement is about PDL satisfaction, not a translation of $\varphi$ into Hennessy–Milner logic. (The separate translation into multimodal logic uses whole programs, not only atomic ones, as modal labels.)
