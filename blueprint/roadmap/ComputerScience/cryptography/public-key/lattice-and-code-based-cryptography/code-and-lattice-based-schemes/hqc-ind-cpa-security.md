# IND-CPA security of HQC under quasi-cyclic syndrome decoding

Assume the decisional quasi-cyclic syndrome decoding problems hold: (2-DQCSD) $(h, x + hy)$ for sparse $(x, y)$ is indistinguishable from $h$ together with a uniform vector of parity $|x| + |h|\,|y| \bmod 2$, and (3-DQCSD) $(h, s, r_1 + hr_2, sr_2 + e)$ for sparse $(r_1, r_2, e)$ is indistinguishable, given uniform $h, s$, from two uniform vectors of parities $|r_1| + |h|\,|r_2|$ and $|s|\,|r_2| + |e| \pmod 2$. Then the HQC encryption core is IND-CPA secure, against adversaries choosing their challenge messages after seeing the public key; the advantage is at most the sum of the two DQCSD advantages (times two).

## Proof sketch

First replace the public key $s$ by a uniform vector (2-DQCSD). Then the pair $(u, v - mG)$ is a 3-DQCSD instance, so it can be replaced by uniform vectors, after which $v$ is uniform and independent of $m$.

## Depends on

- [HQC public-key encryption](../hqc-encryption/hqc-public-key-encryption.md)
- [Public-key eavesdropping experiment](../../../security-games/generic-security-games/pub-cpa-game.md)

## Sources

- C. Aguilar-Melchor, O. Blazy, J.-C. Deneuville, P. Gaborit and G. Zémor, "Efficient Encryption From Random Quasi-Cyclic Codes", IEEE Transactions on Information Theory 64(5), 2018.
