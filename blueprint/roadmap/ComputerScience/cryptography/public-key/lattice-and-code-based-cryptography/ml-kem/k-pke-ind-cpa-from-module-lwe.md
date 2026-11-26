# IND-CPA security of K-PKE from Module-LWE

Consider K-PKE in which the public key contains the matrix $\mathbf{A}$ itself and all noise is sampled with fresh fair coins. For every two-stage IND-CPA adversary $\mathcal{A}$ there are adversaries $\mathcal{B}_1, \mathcal{B}_2$ whose running times exceed that of $\mathcal{A}$ by at most the time of one key generation and one encryption of K-PKE such that

$$
\mathrm{Adv}^{\mathrm{ind\text{-}cpa}}_{\text{K-PKE}}(\mathcal{A}) \le \mathrm{Adv}^{\mathrm{mlwe}}_{k,k,\eta_1}(\mathcal{B}_1) + \mathrm{Adv}^{\mathrm{mlwe}}_{k+1,k,\eta_1,\eta_2}(\mathcal{B}_2),
$$

where the first term is a $k\times k$ Module-LWE advantage with $\mathrm{CBD}_{\eta_1}$ secret and error, and the second a $(k+1)\times k$ Module-LWE advantage with $\mathrm{CBD}_{\eta_1}$ secret and $\mathrm{CBD}_{\eta_2}$ errors (each advantage taken for both challenge bits). Consequently, for a parameter family under which decision Module-LWE holds for these laws, K-PKE is IND-CPA secure. If the noise is instead expanded from seeds by a function $F$, the bound gains two PRF-distinguishing advantages, one for the key-generation seed and one for the encryption coins.

## Proof sketch

Game 1 replaces $\mathbf{t} = \mathbf{A}\mathbf{s} + \mathbf{e}$ by a uniform vector (first Module-LWE instance). Then $\bigl(\binom{\mathbf{t}^{\mathsf T}}{\mathbf{A}^{\mathsf T}}, \binom{\mathbf{t}^{\mathsf T}\mathbf{r} + e_2}{\mathbf{A}^{\mathsf T}\mathbf{r}+\mathbf{e}_1}\bigr)$ is a $(k+1)\times k$ Module-LWE sample with secret $\mathbf{r}$; replacing it by uniform makes the compressed ciphertext independent of the challenge bit. With PRF seed expansion, two further hops replace the expanded noise by fresh coins.

## Depends on

- [K-PKE, the public-key encryption scheme inside ML-KEM](k-pke.md)
- [Decision Module-LWE](../lattice-problems/decision-module-lwe.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)
- [Distinguishing advantage](../../../security-games/games-and-advantages/advantage.md)

## Proof depends on

- [Module-LWE is LWE over the negacyclic ring](../lattice-problems/module-lwe-is-lwe-over-a-ring.md)
- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- Roberto Avanzi et al., "CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)", Third-round submission to the NIST post-quantum cryptography standardization process, dated 4 August 2021.
- National Institute of Standards and Technology, "Module-Lattice-Based Key-Encapsulation Mechanism Standard", National Institute of Standards and Technology, 2024.
