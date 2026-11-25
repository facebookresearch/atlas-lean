# Resolution size and width

Resolution refutes an unsatisfiable CNF formula by deriving the empty clause. Proof complexity measures a refutation by its *size*, the number of lines, and by its *width*, the largest number of literals in a line. Following Ben-Sasson and Wigderson, derivations here allow the resolution rule (from $E \vee x$ and $F \vee \neg x$ derive $E \vee F$) and the weakening rule, and come in two shapes: [tree-like derivations](resolution-tree.md), where every derived line is used once, and general [derivations](is-resolution-derivation.md) given as a sequence of lines. Both are sound ([tree-like](not-cnf-sat.md), [general](not-cnf-sat-of-is-resolution-refutation.md)); completeness is in the [resolution](../resolution/README.md) topic.

Ben-Sasson and Wigderson showed that short refutations are narrow: a [tree-like refutation of size $S$](tree-refutation-narrow.md) yields one of width at most $w(F) + \log_2 S$, and a [general refutation of size $S$](refutation-narrow.md) one of width $w(F) + O(\sqrt{n \ln S})$  for formulas in $n$ variables. Read backwards, a linear lower bound on the refutation width of a formula of bounded width gives an exponential lower bound on its refutation size. This turned the classical size lower bounds for resolution (Haken's pigeonhole bound, Urquhart's bound for Tseitin formulas, the bound of Beame and others for random $3$-CNFs) into width arguments.

- [Width of a clause](width.md)
- [Width of a CNF formula](max-clause-width.md)
- [Tree-like resolution derivation](resolution-tree.md)
- [Size of a tree-like derivation](proof-size.md)
- [Width of a tree-like derivation](proof-width.md)
- [Soundness of tree-like resolution](satisfies.md)
- [A tree-like refutation proves unsatisfiability](not-cnf-sat.md)
- [One step of a resolution derivation](is-resolution-step.md)
- [Resolution derivation](is-resolution-derivation.md)
- [Resolution refutation](is-resolution-refutation.md)
- [Width of a derivation](derivation-width.md)
- [Soundness of resolution derivations](satisfies-of-mem.md)
- [A refutation proves unsatisfiability](not-cnf-sat-of-is-resolution-refutation.md)
- [Ben-Sasson–Wigderson for tree-like resolution](tree-refutation-narrow.md)
- [Ben-Sasson–Wigderson for general resolution](refutation-narrow.md)

## Related topics

- [Resolution](../resolution/README.md): the resolution rule, soundness and refutation completeness, without proof objects.
- [Monotone circuit lower bound for clique](../../../TheoryOfComputation/circuit-complexity/monotone-circuit-lower-bound-for-clique/README.md): lower bounds for a restricted computational model, the circuit-complexity counterpart of lower bounds for a restricted proof system.
