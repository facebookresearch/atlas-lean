# A generic compiler adding certified deletion to any post-quantum encryption

For any post-quantum secure public-key encryption (respectively attribute-based, fully homomorphic, witness, or timed-release encryption), encrypt $m$ by sampling $x,\theta$, preparing $|x\rangle_\theta$, and outputting this state together with a classical encryption of $(\theta,\ m\oplus\bigoplus_{i:\theta_i=0}x_i)$. The result is an encryption scheme of the same type with certified deletion that is *everlasting*: if the certificate (Hadamard-basis outcomes at positions with $\theta_i=1$) is accepted, then the message is statistically hidden from the adversary's residual state, even if the adversary becomes computationally unbounded afterwards. The proof uses a general theorem that certified deletion of the BB84 encoding holds whenever the basis $\theta$ is computationally hidden at deletion time.

## Proof sketch

Prove a "certified deletion lemma": for any distribution where $\theta$ is computationally hidden (encrypted), an adversary that produces a valid certificate cannot later distinguish the encoded bit even with $\theta$ revealed. The argument defers the measurement of $x$ on computational-basis positions, uses semantic security to replace the encryption of $\theta$ while the adversary deletes, and then applies an information-theoretic argument on the deferred measurements.

## Depends on

- [Information-theoretic certified deletion from BB84 states](bb84-certified-deletion.md)
- [Indistinguishability of encryptions with error $\varepsilon$](../security-games/semantic-security-and-indistinguishability/ind-secure.md)

## Proof depends on

- [Information-theoretic certified deletion from BB84 states](bb84-certified-deletion.md)

## Sources

- James Bartusek, Dakshita Khurana, "Cryptography with Certified Deletion", CRYPTO (2023), arXiv:2207.01754.
