# Modes of operation: counter mode and CBC

## Block ciphers and pseudorandom permutations

- [Block cipher](block-cipher.md)

## Counter mode

- [Keystream](keystream.md)
- [Counter-mode encryption](ctr-encrypt.md)
- [Ctr Decrypt](ctr-decrypt.md)
- [Counter-mode decryption inverts encryption](ctr-decrypt-ctr-encrypt.md)
- [Counter mode](ctr-scheme.md)
- [Correctness of counter mode](ctr-scheme-correct.md)
- [Querying a vector of points](query-vec.md)
- [Run query Vec](run-query-vec.md)
- [Counter-mode encryption as an oracle computation](ctr-enc-q.md)
- [Run ctr Enc Q](run-ctr-enc-q.md)
- [Ctr Reduction](ctr-reduction.md)
- [Run ctr Reduction](run-ctr-reduction.md)
- [The real world of the counter-mode reduction](ctr-cpa-game-eq-prf-real.md)
- [Ctr Shift](ctr-shift.md)
- [Shifts at the same starting counter add up](ctr-shift-ctr-shift.md)
- [Ctr Shift zero](ctr-shift-zero.md)
- [Ctr Shift of ne](ctr-shift-of-ne.md)
- [Keystream ctr Shift](keystream-ctr-shift.md)
- [Ctr Fresh](ctr-fresh.md)
- [Ctr Msgs](ctr-msgs.md)
- [Ctr Encrypt ctr Shift of fresh](ctr-encrypt-ctr-shift-of-fresh.md)
- [The challenge is a one-time pad on a fresh counter range](ctr-cpa-guess-flip.md)
- [First-phase computations against counter mode](ctr-comp.md)
- [Fresh counter ranges give an exact half guessing chance](ctr-two-mul-card-wins.md)
- [Few challenge counters overlap the query counters](card-not-ctr-fresh.md)
- [Counter-mode reduction against a random function](ctr-prf-rand-le.md)
- [Concrete CPA advantage bound for counter mode](ctr-cpa-advantage-le.md)

## Cipher block chaining

- [Cbc Chain](cbc-chain.md)
- [CBC unchaining](cbc-unchain.md)
- [CBC unchaining inverts chaining](cbc-unchain-cbc-chain.md)
- [CBC encryption](cbc-encrypt.md)
- [CBC decryption](cbc-decrypt.md)
- [CBC mode](cbc-scheme.md)
- [Correctness of CBC mode](cbc-scheme-correct.md)
- [CBC chain as an oracle algorithm](chain-q.md)
- [Run chain Q](run-chain-q.md)
- [CBC encryption as an oracle computation](cbc-enc-q.md)
- [Cbc Reduction](cbc-reduction.md)
- [The real world of the CBC reduction](cbc-cpa-game-eq-prp-real.md)
- [CBC mode, the PRP step](cbc-cpa-advantage-le.md)
