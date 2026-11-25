# Backward-induction winning region of the fixpoint-free fragment

Let $M$ be a Kripke
model with accessibility relation $R$. For a fixpoint-free formula $\varphi$ and a world $w$,
"$\varphi$ is winning at $w$" is defined by recursion on $\varphi$: an atom $a$ is winning at
$w$ iff $a$ is true at $w$ in $M$; a negated atom $\lnot a$ iff $a$ is not true at $w$; $\bot$
is never winning and $\top$ is always winning; $\varphi \land \psi$ is winning at $w$ iff both
$\varphi$ and $\psi$ are; $\varphi \lor \psi$ iff $\varphi$ or $\psi$ is; $\Box \varphi$ iff
$\varphi$ is winning at every $v$ with $w \mathrel{R} v$; and $\Diamond \varphi$ iff $\varphi$
is winning at some $v$ with $w \mathrel{R} v$.

Verifier has a winning strategy in the model-checking game from the position $(\varphi, w, [])$
with empty stack exactly when $\varphi$ is winning at $w$.
