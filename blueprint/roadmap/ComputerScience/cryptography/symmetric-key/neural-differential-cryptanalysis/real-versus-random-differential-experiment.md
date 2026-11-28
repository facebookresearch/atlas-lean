# Real-versus-random experiments for differential distinguishers

A differential distinguisher for an $r$-round cipher receives a ciphertext pair and guesses whether it encrypts a plaintext pair with fixed nonzero difference $\Delta$ under a uniform key (real) or is a random pair. Two random-pair models are used: the second plaintext fresh and independent, or the ciphertext pair uniform among distinct pairs.

Fix an $r$-round block cipher $E$ with block size $b$ and key size $k$, and a nonzero input difference $\Delta\in\{0,1\}^b$. Draw a uniform key $K$, a uniform plaintext $P$ and a uniform label $Y\in\{0,1\}$; if $Y=1$ output the real pair $(E_K(P),E_K(P\oplus\Delta))$. If $Y=0$, output a random pair according to one of two models:

- **independent-pair model**: $(E_K(P),E_K(P'))$ for a fresh uniform plaintext $P'$; since $E_K$ is a permutation, this pair is uniform on $\{0,1\}^b\times\{0,1\}^b$, and its two blocks coincide with probability $2^{-b}$;
- **distinct-pair model**: an ordered pair uniform among the $2^{2b}-2^b$ pairs of distinct blocks; its difference is uniform on the $2^b-1$ nonzero blocks.

A distinguisher $C$ maps a ciphertext pair to a guess of $Y$. Its *accuracy* is $\Pr[C=Y]$, and its *true positive* and *true negative rates* are $\Pr[C=1\mid Y=1]$ and $\Pr[C=0\mid Y=0]$; with equal priors the accuracy is their mean.

**Blinded real pairs.** For a uniform $M\in\{0,1\}^b$, the pair $(C_0\oplus M,C_1\oplus M)$ has the same difference as $(C_0,C_1)$. A distinguisher that depends only on the difference therefore has accuracy exactly $1/2$ when asked to separate real pairs from blinded real pairs with equal priors.

## Expansion

Gohr generates the training and test data of his neural distinguishers in the independent-pair model (fresh second plaintext, $10^7$ training pairs and test sets of $10^6$ pairs for Speck32/64 with $\Delta=\mathtt{0x0040/0000}$), and uses the distinct-pair model in his difference-table and key-counting analyses. His Table 2 reports accuracies of residual networks above those of the difference-table predictions for 5 to 8 rounds of Speck32/64; these are empirical results for round-reduced Speck32/64. His real-differences experiment trains nothing new: distinguishers trained on the real-versus-random task are evaluated on real versus blinded real pairs, and perform above chance, so they use more than the ciphertext difference. Benamira, Gerault, Peyrin and Tan reproduce this experiment and give an experimental interpretation in terms of differences in earlier rounds.

## Depends on

- [Block cipher (uniform family)](../block-ciphers-and-strong-prps/block-cipher.md)

## Proof depends on

None.

## Sources

- Aron Gohr, "Improving Attacks on Round-Reduced Speck32/64 Using Deep Learning", CRYPTO 2019, Lecture Notes in Computer Science 11693, pp. 150–179, https://doi.org/10.1007/978-3-030-26951-7_6; numbers from IACR ePrint 2019/037, [https://eprint.iacr.org/2019/037](https://eprint.iacr.org/2019/037), Section 2.1 (distinguishers and experiments), Section 3.1, Section 4.3 (data generation), Section 5 and Table 2.
- Adrien Benamira, David Gerault, Thomas Peyrin, Quan Quan Tan, "A Deeper Look at Machine Learning-Based Cryptanalysis", EUROCRYPT 2021, Lecture Notes in Computer Science 12696, https://doi.org/10.1007/978-3-030-77870-5_28 (conference version, [https://iacr.org/archive/eurocrypt2021/126960385/126960385.pdf](https://iacr.org/archive/eurocrypt2021/126960385/126960385.pdf)), Section 3 (Tables 1 and 2).
