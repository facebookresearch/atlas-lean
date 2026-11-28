# Bilinear groups and pairing-based assumptions

Bilinear groups given by explicit exponent isomorphisms from the residues modulo the group order, the consequences of their pairing axiom, and the bilinear Diffie–Hellman, decisional Diffie–Hellman and q-SDH games over them.

## Bilinear group interfaces

- [Bilinear group interfaces](bilinear-group-data.md)
- [Generator of the first source group](g1.md)
- [Generator of the second source group](g2.md)
- [Generator of the target group](g-t.md)
- [One is nonzero modulo the order of a bilinear group](one-ne-zero.md)
- [The target generator is not the identity](g-t-ne-one.md)
- [The pairing of the generators is the target generator](e-g1-g2.md)
- [The pairing of the generators is nontrivial](e-g1-g2-ne-one.md)
- [The pairing is multiplicative in its first argument](map-mul-left.md)
- [The pairing is multiplicative in its second argument](map-mul-right.md)
- [The pairing with the identity on the left is trivial](e-one-left.md)
- [The pairing with the identity on the right is trivial](e-one-right.md)
- [The left kernel of the pairing is trivial](eq-one-of-forall-e-eq-one-left.md)
- [The right kernel of the pairing is trivial](eq-one-of-forall-e-eq-one-right.md)
- [Power law for the pairing](e-pow.md)
- [Toy exponent model of a bilinear group](toy-model.md)

## The bilinear Diffie–Hellman game

- [Bilinear Diffie–Hellman win experiment](bdh-win.md)
- [Bilinear Diffie–Hellman game](bdh-game.md)
- [Bilinear Diffie–Hellman advantage](bdh-advantage.md)
- [An adversary that always wins the BDH experiment wins the BDH game surely](bdh-game-eq-pure-true.md)
- [Discrete-logarithm adversary for the toy BDH game](toy-bdh-adversary.md)
- [The discrete-logarithm adversary always wins the toy BDH experiment](toy-bdh-win.md)
- [The toy BDH game is won with probability one](toy-bdh-advantage-eq-one.md)

## Decisional Diffie–Hellman in the source groups

- [Real decisional Diffie–Hellman game in the first source group](ddh1-real-game.md)
- [Random decisional Diffie–Hellman game in the first source group](ddh1-random-game.md)
- [Decisional Diffie–Hellman advantage in the first source group](ddh1-advantage.md)
- [Real decisional Diffie–Hellman game in the second source group](ddh2-real-game.md)
- [Random decisional Diffie–Hellman game in the second source group](ddh2-random-game.md)
- [Decisional Diffie–Hellman advantage in the second source group](ddh2-advantage.md)
- [Advantage bound for a pair of decisional Diffie–Hellman distinguishers](sxdh-adv-bound.md)

## The q-SDH game

- [q-SDH win experiment](sdh-win.md)
- [q-SDH game](sdh-game.md)
- [q-SDH advantage](sdh-advantage.md)
- [q-SDH check at a unit denominator](sdh-check-iff.md)
- [q-SDH check at prime order](sdh-check-iff-prime.md)
- [An adversary that always wins the q-SDH experiment wins the q-SDH game surely](sdh-game-eq-pure-true.md)
- [Discrete-logarithm adversary for the q-SDH game](sdh-decoding-adversary.md)
- [The discrete-logarithm adversary always wins the q-SDH experiment](sdh-win-decoding.md)
- [The q-SDH game is won with probability one by a discrete-logarithm adversary](sdh-advantage-decoding-eq-one.md)
- [The q-SDH advantage is nonnegative](sdh-advantage-nonneg.md)
- [The q-SDH advantage is at most one](sdh-advantage-le-one.md)
