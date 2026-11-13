# Fragment moves between embedded positions are game moves

Let $M$ be a Kripke model,
$\mathrm{env}$ an environment, $\varphi, \varphi'$ fixpoint-free formulas and $w, w'$ worlds. If
the totalized fragment game has a move from the embedded position $(\varphi, w)$ to the embedded
position $(\varphi', w')$, then the model-checking game has a move from $(\varphi, w, [])$ to
$(\varphi', w', [])$, where the fixpoint-free formulas are viewed as μ-calculus formulas and
$[]$ is the empty binder stack.
