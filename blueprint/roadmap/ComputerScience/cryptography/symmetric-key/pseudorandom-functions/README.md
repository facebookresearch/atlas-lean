# Pseudorandom functions

## The PRF experiment

- [Real world of the PRF experiment](prf-real.md)
- [Random world of the PRF experiment](prf-rand.md)
- [PRF advantage](prf-advantage.md)
- [Asymptotic PRF security relative to `Admissible`](prfsecure.md)

## The MAC from a PRF

- [Winning the forgery game](mac-wins.md)
- [The MAC forgery experiment](mac-game.md)
- [The distinguisher built from a forger](mac-reduction.md)
- [The MAC reduction in the real PRF world](mac-game-eq-prf-real.md)
- [Counting forgeries against a random function](card-mac-wins-mul-le.md)
- [Forging against a random function](prf-rand-mac-reduction-le.md)
- [The MAC from a PRF, concrete security](mac-game-le.md)

## CPA encryption from a PRF

- [Encryption from a keyed function](encrypt.md)
- [Decryption with a keyed function](decrypt.md)
- [Correctness of encryption with a keyed function](decrypt-encrypt.md)
- [Selecting the challenge message by a bit](pick.md)
- [Running an algorithm against the bounded encryption oracle](run-enc.md)
- [CPA adversary](cpaadversary.md)
- [The adversary's guess in the CPA experiment](cpa-guess.md)
- [The CPA experiment](cpa-game.md)
- [CPA advantage](cpa-advantage.md)
- [Simulating the encryption oracle with a function oracle](sim-enc.md)
- [The PRF distinguisher built from a CPA adversary](cpa-reduction.md)
- [The CPA reduction is exact with the real oracle](cpa-game-eq-prf-real.md)
- [The encryption oracle depends only on the encryption randomness](run-enc-congr.md)
- [The CPA reduction against a random function](prf-rand-cpa-reduction.md)
- [CPA encryption from a PRF, concrete security](cpa-advantage-le.md)
