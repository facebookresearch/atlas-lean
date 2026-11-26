# Program behaviors and semantic preservation

Program behaviors and semantic preservation after X. Leroy, Formal verification of a realistic compiler, Commun. ACM 52(7) (2009), Section 2.1, in an adapted model: a behavior is termination or going wrong after a finite trace of labels, or reaction with an infinite trace; source and target are two operational semantics, each with its own transition relation and final configurations, over a common configuration type and a common label type (homogeneous preservation: the types are shared, the transition relations need not be), every label is observable, silent divergence (a finite trace followed by infinitely many silent steps) is not a behavior, and preservation relates two given configurations; no compilation function is involved. CompCert's model, by contrast, relates different languages and includes silent divergence.

- [Behavior](behavior.md)
- [Behaviors of a configuration](beh.md)
- [Termination with a given trace](terminates-mem-iff.md)
- [Reaction with a given label stream](reacts-mem-iff.md)
- [Going wrong with a given trace](goes-wrong-mem-iff.md)
- [Terminates or goes Wrong or reacts](terminates-or-goes-wrong-or-reacts.md)
- [Exists behavior](exists-behavior.md)
- [Preserves1](preserves1.md)
- [Preserves2](preserves2.md)
- [Safe target](safe-target.md)
- [Trans](trans.md)
- [Nondet Toy Cfg](nondet-toy-cfg.md)
- [Nondeterministic toy semantics](nondet-toy.md)
- [Deterministic toy semantics](det-toy.md)
- [Form (1) preservation fails from the nondeterministic to the deterministic toy](preserves1-fails-nondet-to-det.md)
- [Form (2) preservation holds from the nondeterministic to the deterministic toy](preserves2-nondet-to-det.md)
