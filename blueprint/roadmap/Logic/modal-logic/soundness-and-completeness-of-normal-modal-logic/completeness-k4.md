# Strong completeness of K4

Let $\Gamma$ be a set of formulas and $\varphi$ a formula. Suppose that for every Kripke model
with transitive accessibility relation whose worlds form a type in the universe of the atoms, and
every world $w$ of it at which all formulas of $\Gamma$ hold, $\varphi$ holds at $w$. Then
$\varphi$ is deducible from $\Gamma$ in K4.

Proof: the canonical model of K4 is transitive, because K4 proves every instance of axiom 4; a set
$\Gamma$ that does not deduce $\varphi$ extends to a maximal consistent set omitting $\varphi$, a
world of the canonical model at which $\Gamma$ holds and $\varphi$ fails (truth lemma).

## Informally uses

- [Completeness relative to the canonical model](of-canonical-model.md): a set that does not
  deduce $\varphi$ is satisfied at a world of the canonical model where $\varphi$ fails.
- [Truth lemma](satisfies-canonical-iff.md): truth in the canonical model is membership.

## Background

- [Strong completeness of K](completeness-k.md): the same canonical-model argument, without the
  transitivity condition.

## Sources

- P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*, Cambridge University Press, 2001, §4.2.
