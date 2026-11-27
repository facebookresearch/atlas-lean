# Soundness error for false statements

For a [specially sound](special-sound.md) Sigma protocol and a statement $x$ with no witness at all,
every cheating prover is accepted in the [cheating experiment](cheat-game.md) with probability at most
$1 / \lvert \mathrm{Ch} \rvert$: for each commitment it can answer at most one challenge.

This is soundness for the language of true statements, not knowledge soundness: the hypothesis says
that $x$ is false, which is much stronger than saying that the prover does not know an existing
witness. In the Schnorr setting with a generator of the order-$q$ subgroup every statement has a
witness, so the hypothesis never holds there, and this result does not model the impersonation attack
of Katz and Lindell's Theorem 12.11.

## Informally uses

- [A witness from two accepting transcripts](exists-witness-of-verify-of-verify.md)
