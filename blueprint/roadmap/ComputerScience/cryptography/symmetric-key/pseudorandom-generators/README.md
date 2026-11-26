# Pseudorandom generators

## The PRG game

- [Distinguisher for a pseudorandom generator](distinguisher.md)
- [Real world of the PRG experiment](prg-real.md)
- [Random world of the PRG experiment](prg-rand.md)
- [PRG advantage](prg-advantage.md)
- [Expanding generator families](prgexpanding.md)
- [Pseudorandomness relative to a class of distinguishers](prgindistinguishable.md)
- [Asymptotic PRG security relative to a class of distinguishers](prgsecure.md)
- [Families that fail to expand are not PRGs](not-prg-secure-of-card-le.md)

## The stream cipher

- [The stream cipher](stream-cipher.md)
- [Correctness of the stream cipher](stream-cipher-correct.md)
- [The CPA experiment with a given keystream](exp-run.md)
- [PRG distinguisher from an adversary against the stream cipher](cpa-reduction.md)
- [The CPA experiment against the stream cipher in closed form](cpa-exp-stream-cipher.md)
- [The real PRG world is the CPA experiment](cpa-game-stream-cipher-eq-prg-real.md)
- [The random PRG world is a fair coin](prg-rand-cpa-reduction.md)
- [The stream cipher is eavesdropping-secure if the PRG is pseudorandom](cpa-advantage-stream-cipher-eq.md)
- [Asymptotic eavesdropping security of the stream cipher](eav-secure-stream-cipher.md)
- [Asymptotic eavesdropping security of the stream cipher from a PRG](eav-secure-stream-cipher-of-prg-secure.md)

## The stream cipher is not CPA-secure

- [The replay attack](replay-attack.md)
- [The replay attack makes one query](replay-attack-query-bounded.md)
- [The stream cipher is not CPA-secure](cpa-advantage-replay-attack.md)
- [No stream cipher family is polynomial-query CPA-secure](not-poly-query-cpasecure-stream-cipher.md)

## Pseudoentropy and generic constructions

- [Computational pseudoentropy](computational-pseudoentropy.md)
- [Pseudorandom generators exist if and only if one-way functions exist](pseudorandom-generators-exist-if-and-only-if.md)
- [The generator of a keyed function at fixed points](prg-of-prf.md)
- [The PRF distinguisher built from a PRG distinguisher](prg-of-prfreduction.md)
- [Pseudorandom generators from pseudorandom functions](pseudorandom-generators-from-pseudorandom.md)
- [Asymptotic PRG security from a PRF](prg-secure-prg-of-prf.md)
- [Sequential and parallel composition of pseudorandom generators](sequential-and-parallel-composition-of.md)
