# Soundness error of sequential repetition

Let a Sigma protocol with a finite set $\mathrm{Ch}$ of challenges be specially sound, and let $x$ be
a statement with no witness. Then every adaptive cheating prover with coins in a finite type is
accepted in all $m$ rounds of the [sequential experiment](seq-cheat-game.md) with probability at most
$1 / \lvert \mathrm{Ch} \rvert^m$.

This is soundness for the language of true statements, not knowledge soundness, as for the
[one-round bound](win-prob-cheat-game-le.md).

## Informally uses

- [At most one accepted challenge sequence](all-accept-subsingleton.md): for each choice of coins at
  most one challenge sequence out of $\lvert \mathrm{Ch} \rvert^m$ is accepted.

## Sources

- O. Goldreich, S. Micali and A. Wigderson, "Proofs that yield nothing but their validity or all languages in NP have zero-knowledge proof systems", J. ACM 38 (1991), 691-729, Section 2.2 (Protocol 2: "the following four steps are executed $m$ times, each time using
  independent random coin tosses").
