# Key-bit recovery by linear cryptanalysis

Let $E : \{0,1\}^h \times \{0,1\}^n \to \{0,1\}^n$ be a keyed function satisfying a *linear relation* with masks $(S_0, S_1, S_2)$ and bias $\varepsilon > 0$: for a uniform key-independent input $x$, $\Pr[\langle S_0, x\rangle \oplus \langle S_1, E(k, x)\rangle = \langle S_2, k\rangle] \ge \tfrac12 + \varepsilon$ for every key $k$. Given $t$ independent uniformly random plaintext–ciphertext pairs, the majority vote of $\langle S_0, x_j\rangle \oplus \langle S_1, E(k, x_j)\rangle$ equals the key bit $\langle S_2, k\rangle$ with probability at least

$$
1 - e^{-2t\varepsilon^2}.
$$

Hence $t = O(1/\varepsilon^2)$ known plaintexts recover one bit of key information with constant error.

## Proof sketch

The votes are independent Bernoulli variables with mean at least $1/2 + \varepsilon$; the majority errs only if their average deviates by $\varepsilon$, which Hoeffding's inequality bounds.

## Depends on

- [Luby–Rackoff theorem](../pseudorandom-constructions/lubyrackoff-theorem.md)

## Sources

- Mitsuru Matsui, "Linear Cryptanalysis Method for DES Cipher", Advances in Cryptology – EUROCRYPT '93, LNCS 765, Springer, 1994, pp. 386–397, Algorithm 1.
- Wassily Hoeffding, "Probability Inequalities for Sums of Bounded Random Variables", Journal of the American Statistical Association 58, 1963, pp. 13–30.
