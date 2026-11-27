# A generic compiler adding certified deletion to any post-quantum encryption

For any post-quantum semantically secure public-key encryption scheme (and analogously attribute-based, fully homomorphic, witness, or timed-release encryption), encrypt a bit $b$ by sampling $x,\theta\leftarrow\{0,1\}^{\lambda}$ and outputting $|x\rangle_\theta$ together with a classical encryption of $(\theta,\ b\oplus\bigoplus_{i:\theta_i=0}x_i)$, with verification key $(x,\theta)$. Deletion measures $|x\rangle_\theta$ in the Hadamard basis, and a certificate $x'$ is accepted iff $x'_i=x_i$ for every $i$ with $\theta_i=1$. The result is an encryption scheme of the same type with *everlasting* certified deletion: for a QPT adversary that outputs a certificate and a residual state, the experiment that outputs the residual state when the certificate is accepted and $\bot$ otherwise has trace distance $\mathrm{negl}(\lambda)$ between $b=0$ and $b=1$, so the outputs remain indistinguishable even to a later computationally unbounded distinguisher; and the adversary's output together with the verification bit computationally hides $b$. Multi-bit messages are handled by a separate generalization. The proof uses a general theorem that certified deletion of the BB84 encoding of one bit holds whenever the basis $\theta$ is computationally hidden at deletion time.

## Proof sketch

Prove a "certified deletion lemma" (Bartusek–Khurana, Theorem 3.1): if $Z_\lambda(\theta,b',A)$ is semantically secure with respect to $\theta$ against a class of adversaries, then for every adversary in that class given $Z_\lambda(\theta,b\oplus\bigoplus_{i:\theta_i=0}x_i,|x\rangle_\theta)$, the distribution that outputs its residual state if its certificate agrees with $x$ on $\{i:\theta_i=1\}$ and $\bot$ otherwise is negligibly close in trace distance for $b=0$ and $b=1$. The argument defers the measurement of $x$ on computational-basis positions, uses semantic security to replace the encryption of $\theta$ while the adversary deletes, and then applies an information-theoretic argument on the deferred measurements.

## Depends on

- [Indistinguishability of encryptions with error $\varepsilon$](../security-games/semantic-security-and-indistinguishability/ind-secure.md)
- [Encryption with certified deletion](certified-deletion.md)

## Proof depends on

- [Information-theoretic certified deletion from BB84 states](bb84-certified-deletion.md)

## Sources

- James Bartusek, Dakshita Khurana, "Cryptography with Certified Deletion", CRYPTO (2023), arXiv:2207.01754.
