# Merkle signature scheme

## The scheme

- [Merkle signature](signature.md)
- [Collision of a hash function](collides.md)
- [Leaves of a Merkle signature tree](leaves-of.md)
- [Root over a family of Lamport public keys](root-of.md)
- [Stateful Merkle signer](signer-of.md)
- [Lamport public keys of a family of secret keys](lamport-keys.md)
- [Public key of the Merkle signature scheme](public-key.md)
- [Merkle signing](sign.md)
- [Merkle signature verification](verify.md)
- [One leaf per Lamport key](length-leaves-of.md)
- [The leaves are the hashed keys](get-elem-leaves-of.md)
- [Merkle levels of a nonempty list are nonempty](iterate-level-ne-nil.md)
- [Nonempty lists of leaves have a root](exists-root-eq-some.md)
- [The signer answers while keys remain](is-some-sign.md)
- [Correctness of Merkle signatures](verify-sign.md)
- [Soundness of Merkle signature verification](verify-sound.md)

## The forgery experiment

- [Forger against Merkle signatures](forger.md)
- [Run of a Merkle forger](run.md)
- [Winning a Merkle forgery](win.md)
- [The signature carries the honest key](key-matches.md)
- [Merkle signature forgery experiment](forge-game.md)
- [Key-mismatch event](key-mismatch-game.md)
- [The key-mismatch event in terms of winning](key-mismatch-game-eq.md)
- [Key mismatches imply collisions](collision-of-key-mismatch-game.md)
- [No key mismatches for injective hashes](win-prob-key-mismatch-game-eq-zero.md)

## The reduction to Lamport one-time security

- [The reduction's Lamport public keys](sim-keys.md)
- [The reduction's signing oracle](red-signer.md)
- [The reduction's Lamport signing query](red-choose.md)
- [The reduction's forgery](red-forge.md)
- [Reduction from Merkle forgeries to Lamport forgeries](reduction.md)
- [Planting a challenge key](sim-keys-eq.md)
- [The reduction signs like the honest signer](red-signer-eq.md)
- [Core of the reduction to Lamport](reduction-wins.md)

## Forgery bound up to the key-mismatch event

- [Forgery bound up to the key-mismatch event](win-prob-forge-game-le.md)
- [Reduction to Lamport for injective hashes](win-prob-forge-game-le-of-injective.md)
- [Bad-event bound from one-wayness](win-prob-forge-game-le-invert.md)
