# Linear temporal logic

- [Formulas of linear temporal logic](formula.md)
- [Falsity in LTL](bot.md)
- [Disjunction in LTL](or.md)
- [Implication in LTL](imp.md)
- [Bi-implication in LTL](iff.md)
- [The eventually operator of LTL](eventually.md)
- [The always operator of LTL](always.md)
- [The release operator of LTL](release.md)
- [Satisfaction of LTL formulas on ω-words](satisfies.md)
- [Satisfaction at a position](satisfies-at.md)
- [Language of an LTL formula](language.md)
- [Satisfaction at position zero](satisfies-at-zero.md)
- [Satisfaction on a suffix](satisfies-at-drop.md)
- [Satisfaction of an atom](atom-iff.md)
- [Falsity is never satisfied](bot-iff.md)
- [Semantics of eventually](eventually-iff.md)
- [Semantics of release](release-iff.md)
- [Next is self-dual](not-next.md)
- [Expansion law for until](until-expansion.md)
- [Expansion law for release](release-expansion.md)
- [Idempotence of always](always-always.md)
- [Always eventually means infinitely often](always-eventually-iff.md)
- [Eventually always means from some point on](eventually-always-iff.md)
- [Satisfaction of an atom at a position](satisfies-at-atom.md)
- [Relabelling the letters of an ω-word](satisfies-map.md)
- [Membership in the language of a formula](mem-language.md)

## Token encoding

- [Token encoding of an LTL formula](tokens.md)
- [One token per occurrence](length-tokens.md)
- [Fuelled parsing of LTL tokens](parse-fuel.md)
- [Parsing inverts the token encoding](parse-fuel-tokens.md)
- [Decoding a token list](decode-list.md)
- [Decoding inverts the token encoding](decode-list-tokens.md)
- [Parsing reads only token encodings](tokens-append-of-parse-fuel-eq-some.md)
- [Decoding reads only token encodings](tokens-eq-of-decode-list-eq-some.md)
- [Decoding accepts exactly the token encodings](decode-list-eq-some-iff.md)

## Linear temporal logic on runs

- [Satisfaction of LTL formulas on runs](satisfies-2.md)
- [Satisfaction at a position of a run](satisfies-at-2.md)
- [An atom at a position is the valuation at that state](atom-at-iff.md)
- [Expansion law for until on runs](until-expansion-2.md)
- [Universal path quantifier over runs](forall-runs.md)
- [Existential path quantifier over runs](exists-run.md)
- [Safety from reachability](forall-runs-always-atom-of-reachable.md)
- [Reachability from safety on infinite runs](reachable-of-forall-runs-always-atom.md)

## Related topics

- [Büchi automata for a fragment of linear temporal logic](../b-chi-automata-for-a-fragment-of-linear-temporal/README.md): direct automata for invariants, recurrence, persistence and a safety fragment.
- [Model checking for linear temporal logic](../model-checking-for-linear-temporal-logic/README.md): the automata-theoretic treatment of LTL: the Vardi–Wolper translation into Büchi automata, satisfiability as nonemptiness, and model checking as language inclusion.
