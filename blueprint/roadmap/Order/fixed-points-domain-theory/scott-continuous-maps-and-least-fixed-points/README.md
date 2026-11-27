# Scott-continuous maps and least fixed points

A map between partial orders is Scott-continuous when it preserves suprema of directed sets; the domains are directed-complete partial orders (dcpos), called pointed when they have a least element. The continuous maps between dcpos form a dcpo with pointwise directed suprema. Between complete lattices they form a complete lattice, with pointwise joins. Every continuous self-map of a pointed dcpo has a least fixed point, the supremum of the Kleene chain $\bot \le f(\bot) \le f(f(\bot)) \le \cdots$ (Kleene's fixed-point theorem; S. Abramsky and A. Jung, *Domain Theory*, 1994, Proposition 2.1.18 and Theorem 2.1.19).

The denotational semantics of PCF uses the ω-chain variant: ω-complete partial orders and maps preserving suprema of ω-chains, for which the same results hold. On a dcpo, every Scott-continuous map is ω-Scott-continuous.

## Directed suprema

- [The pointwise directed supremum of Scott-continuous maps is Scott-continuous](scott-continuous-s-sup-image-of-directed.md)
- [Directed suprema of Scott-continuous maps are computed pointwise](is-lub-s-sup-image-of-directed-on.md)
- [Arbitrary pointwise suprema of Scott-continuous maps between complete lattices](scott-continuous-s-sup.md)
- [Kleene's fixed-point theorem for pointed dcpos](map-i-sup-iterate-bot.md)
- [Kleene's fixed point is the least prefixed point](i-sup-iterate-bot-le.md)
- [Kleene's supremum for dcpos is the least fixed point of the ω-chain construction](i-sup-iterate-bot-eq-lfp.md)

## ω-chains

- [Scott continuity into a function space is checked pointwise](scott-continuous-of-apply.md)
- [Currying of Scott-continuous maps](curry.md)
- [Least fixed point of a Scott-continuous map](lfp.md)
- [The least fixed point is a fixed point](lfp-eq.md)
- [The least fixed point lies below every prefixed point](lfp-le.md)
- [Scott continuity of the least-fixed-point operator](lfp-scott-continuous.md)
- [The least-fixed-point operator as a Scott-continuous map](lfp-hom.md)

## Related topics

- [Continuous lattices](../continuous-lattices/README.md): Scott's class of domains, defined by the way-below relation.
- [Scott's graph model](../scott-s-graph-model/README.md): a concrete universal domain, $P(\omega)$, where these notions become finitary.
- [PCF and computational adequacy](../../../ComputerScience/programming-language-semantics/pcf-and-computational-adequacy/README.md): the denotational semantics built on the ω-chain variant.
