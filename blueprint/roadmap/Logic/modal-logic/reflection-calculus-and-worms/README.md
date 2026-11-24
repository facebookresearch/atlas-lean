# Reflection calculus and worms

Japaridze's polymodal provability logic GLP has a box $[n]$ for each natural number $n$; in its
arithmetical interpretation $\langle n \rangle\varphi$ is the $n$-consistency of
$\mathrm{PA} + \varphi$, equivalently the uniform reflection principle for $\Pi_{n+1}$-sentences.
GLP is decidable and arithmetically complete but has no adequate Kripke semantics. Beklemishev's
Reflection Calculus RC keeps only the strictly positive fragment: formulas built from atoms and
$\top$ by $\wedge$ and the diamonds $\langle n \rangle$, and sequents $A \vdash B$ between them. RC
axiomatizes the strictly positive fragment of GLP (Dashkov), is complete for a natural class of
Kripke frames, and is decidable in polynomial time, yet it retains the proof-theoretic applications
of GLP.

The closed conjunction-free formulas, the worms $\langle n_1 \rangle \cdots \langle n_k \rangle\top$,
ordered by $\alpha <_0 \beta$ iff $\beta \vdash \langle 0 \rangle\alpha$, form an ordinal notation
system of order type $\varepsilon_0$. With the reduction property of reflection principles this
gives Beklemishev's analysis of Peano arithmetic: transfinite induction along $<_0$ proves
$\mathrm{Con}(\mathrm{PA})$, PA is $\Pi^0_{n+1}$-conservatively equivalent to iterated reflection
along $\varepsilon_0$, and the combinatorial "Every Worm Dies" principle is independent of PA. The
pages below cover the calculus, positive replacement, closure under substitution, Kripke
soundness and completeness, and the order of the worms.

Sources: L. D. Beklemishev, "Positive provability logic for uniform reflection principles",
arXiv:1304.4396v3 (2013), *Annals of Pure and Applied Logic* 165 (2014); L. D. Beklemishev,
"Provability algebras: an overview and current progress", slides, 2012.

## Calculus

- [Strictly positive formulas](formula.md)
- [The Reflection Calculus RC](derives.md)
- [Substitution in strictly positive formulas](subst.md)
- [Positive replacement](subst-left-right.md)
- [Closure under substitution](substitution.md)

## Kripke semantics

- [RC-frame](is-frame.md)
- [Truth of a strictly positive formula in a Kripke model](satisfies.md)
- [Soundness of RC for RC-models](sound.md)
- [Kripke completeness of RC](derives-iff-forall-frame.md)

## Worms

- [Worm](worm.md)
- [The order `<₀` on worms](worm-lt.md)
- [The worms `0⋯0` lie below the worm `1`](replicate-zero-one.md)
- [Irreflexivity of `<₀` at the worm `0`](not-worm-lt-zero-zero.md)
- [Worms have order type `ε₀`](exists-worm-ordinal.md)

## Related topics

- [Provability logic GL](../provability-logic-gl/README.md): GLP has a copy of GL for each of its
  modalities; RC is the strictly positive fragment of GLP.
