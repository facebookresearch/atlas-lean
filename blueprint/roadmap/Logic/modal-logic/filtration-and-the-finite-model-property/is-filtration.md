# Filtration relations

Let $M$ be a Kripke model, $\varphi$ a modal formula, $\Sigma$ the
set of subformulas of $\varphi$, and for a world $w$ let $[w]$, the type of $w$, be the set of
formulas of $\Sigma$ true at $w$ in $M$. A relation $R$ on finite sets of formulas is a
filtration of $M$ through $\Sigma$ when (min) for all worlds $w, v$ related in $M$, the pair
$([w], [v])$ is in $R$, and (max) for all worlds $w, v$ with $([w], [v]) \in R$ and every
formula $\psi$ with $\Box\psi \in \Sigma$, if $\Box\psi$ holds at $w$ in $M$ then $\psi$ holds at
$v$ in $M$.

These are conditions (ii) and (iii) of Blackburn–de Rijke–Venema, Definition 2.36, in $\Box$
form; conditions (i) and (iv) (worlds are the $\Sigma$-types, atoms of $\Sigma$ true where they
belong) are built into the construction of the finite model.
