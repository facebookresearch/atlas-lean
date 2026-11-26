# Program behaviors and semantic preservation

Program behaviors and semantic preservation after X. Leroy, Formal verification of a realistic compiler, Commun. ACM 52(7) (2009), Section 2.1, in an adapted model: a behavior is termination or going wrong after a finite trace of labels, or reaction with an infinite trace; source and target are two operational semantics, each with its own transition relation and final configurations, over a common configuration type and a common label type (homogeneous preservation: the types are shared, the transition relations need not be), every label is observable, silent divergence (a finite trace followed by infinitely many silent steps) is not a behavior, and preservation relates two given configurations; no compilation function is involved. CompCert's model, by contrast, relates different languages and includes silent divergence.

- [Behavior](behavior.md)
- [Behaviors of a configuration](beh.md)
- [Terminates mem iff](terminates-mem-iff.md)
- [Reacts mem iff](reacts-mem-iff.md)
- [Goes Wrong mem iff](goes-wrong-mem-iff.md)
- [Terminates or goes Wrong or reacts](terminates-or-goes-wrong-or-reacts.md)
- [Exists behavior](exists-behavior.md)
- [Preserves1](preserves1.md)
- [Preserves2](preserves2.md)
- [Safe target](safe-target.md)
- [Trans](trans.md)
- [Nondet Toy Cfg](nondet-toy-cfg.md)
- [Nondet Toy](nondet-toy.md)
- [Det Toy](det-toy.md)
- [Preserves1 fails nondet to det](preserves1-fails-nondet-to-det.md)
- [Preserves2 nondet to det](preserves2-nondet-to-det.md)
