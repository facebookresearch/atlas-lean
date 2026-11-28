# Monadic MAC forger

Fix a [sampling family](sample-fam.md), a type $M$ of messages and a type $T$ of tags. A monadic MAC forger is one computation over the tagging-oracle signature (queries $m \in M$ answered in $T$) extended by the sampling operations of the family. It may sample and query the tagging oracle at any point, and returns a pair $(m, t) \in M \times T$. The type does not require $(m, t)$ to verify or $m$ to be fresh; the [forgery experiment](m-mac-game.md) tests both (Katz and Lindell, Definition 4.2).
