# Equilibrium search problems

Search relations over explicit game encodings: BIMATRIX relates a bimatrix game with rational payoffs to its mixed Nash equilibria
with rational probabilities; for $k \ge 3$ players exact equilibria may require irrational probabilities, so
$\varepsilon$-NASH$_k$ relates a $k$-player game with rational payoffs and a rational $\varepsilon > 0$, given in binary, to its rational mixed profiles that
are $\varepsilon$-Nash equilibria, meaning that no player gains more than $\varepsilon$ in expected payoff by a unilateral deviation to a pure strategy
(an additive notion, weaker than the well-supported $\varepsilon$-equilibria of Daskalakis, Goldberg and Papadimitriou); PURE-POTENTIAL relates a game
given together with an exact (cost) potential to its pure Nash equilibria. The relations are not polynomially balanced as stated: in
the bimatrix game whose payoffs are all zero every rational profile is a witness, of arbitrarily large bit size, so membership
statements in a search-problem class are made for their restrictions to candidates of polynomially bounded bit size. The END-OF-LINE problem and the class PPAD are related classification context, not premises of these definitions.

## Depends on

- [Explicit encoding and size of finite games](explicit-encoding-and-size-of-finite-games.md)
- [Expected payoff of a mixed profile](nash-s-theorem/expected-payoff.md)
- [Mixed Nash equilibrium](nash-s-theorem/is-mixed-nash.md)
- [Exact potential of a finite game](potential-games/is-exact-potential-2.md)
- [Pure Nash equilibrium](potential-games/is-pure-nash.md)

## Sources

- CS364A Lecture #20: Mixed Nash Equilibria and PPAD-Completeness — Tim Roughgarden, Stanford University (2013), Sections 1–2 (the bimatrix problem and search problems). <https://theory.stanford.edu/~tim/f13/l/l20.pdf>
- The Complexity of Computing a Nash Equilibrium — Daskalakis, Goldberg, Papadimitriou, STOC 2006, Section 1 (three-player games with only irrational equilibria, after Nash) and Section 2 (search problems, r-Nash with a binary accuracy specification). <http://people.csail.mit.edu/costis/papers/ppad.pdf>
