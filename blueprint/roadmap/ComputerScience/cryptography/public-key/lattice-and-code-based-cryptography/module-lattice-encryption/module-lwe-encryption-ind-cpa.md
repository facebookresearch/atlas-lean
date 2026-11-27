# IND-CPA security of Module-LWE encryption

For Module-LWE encryption with secret law $\chi_s$ and error law $\chi_e$, every IND-CPA adversary $\mathcal{A}$ has advantage at most

$$
\mathrm{Adv}^{\mathrm{mlwe}}_{k \times k}(\mathcal{B}_1) + \mathrm{Adv}^{\mathrm{mlwe}}_{(k+1) \times k}(\mathcal{B}_2)
$$

(for each challenge bit) for explicit reductions $\mathcal{B}_1, \mathcal{B}_2$: the first instance replaces the public key $\mathbf{b} = \mathbf{A}\mathbf{s} + \mathbf{e}$ by a uniform vector, and the second replaces the ciphertext $(\mathbf{A}^{\mathsf T}\mathbf{r} + \mathbf{e}_1, \mathbf{b}^{\mathsf T}\mathbf{r} + e_2)$, a $(k+1)\times k$ Module-LWE sample with secret $\mathbf{r}$ for the stacked matrix $\binom{\mathbf{b}^{\mathsf T}}{\mathbf{A}^{\mathsf T}}$, by a uniform pair. Conditioning the public-key generator on the sampled secret retains the correct joint law of secret and public key, and forgetting the secret gives exactly the public encryption view.

## Proof sketch

Two hybrid hops; in the final game the ciphertext is uniform and independent of the message.

## Depends on

- [Ring-LWE and Module-LWE public-key encryption](module-lwe-encryption.md)
- [Decision Module-LWE](../lattice-problems/decision-module-lwe.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)

## Proof depends on

- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- Vadim Lyubashevsky, Chris Peikert and Oded Regev, "On Ideal Lattices and Learning with Errors over Rings", Advances in Cryptology – EUROCRYPT 2010, 2010.
- Adeline Langlois and Damien Stehlé, "Worst-Case to Average-Case Reductions for Module Lattices", Designs, Codes and Cryptography, 2015.
