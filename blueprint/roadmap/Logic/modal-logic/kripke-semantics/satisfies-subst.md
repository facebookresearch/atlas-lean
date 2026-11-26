# Semantic substitution lemma

Let $M$ be a Kripke model, $p$ an atom and $\varphi$, $\psi$ formulas. For every world $w$,

$$M, w \models \varphi[p := \psi] \iff M[p \mapsto \{v : M, v \models \psi\}], w \models \varphi.$$

Proof: induction on $\varphi$; the relation is unchanged, so the $\Box$ case is immediate.

## Background

- [Substitution of a formula for an atom](subst.md)
- [Kripke model with one atom reinterpreted](update-atom.md)

## Sources

- P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001
  (uniform substitution).
