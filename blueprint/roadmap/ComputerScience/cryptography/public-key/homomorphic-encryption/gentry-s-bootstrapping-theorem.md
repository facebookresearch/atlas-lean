# Gentry's bootstrapping theorem

Let $\mathcal{E}$ be a public-key encryption scheme with plaintext space $P$, decryption circuit $D_\mathcal{E}$, and let $C_\mathcal{E}$ be the set of circuits that $\mathcal{E}$ can
*compactly evaluate*: homomorphic evaluation of a circuit in $C_\mathcal{E}$ on ciphertexts yields a ciphertext of bounded size that decrypts to the circuit's output.
For a set $\Gamma$ of gates over $P$ that includes the trivial gate, a *$g$-augmented decryption circuit* joins copies of $D_\mathcal{E}$ by a single gate $g \in \Gamma$, and
$D_\mathcal{E}(\Gamma)$ is the set of these circuits. $\mathcal{E}$ is *bootstrappable* with respect to $\Gamma$ if $D_\mathcal{E}(\Gamma) \subseteq C_\mathcal{E}$.

**Theorem (Gentry).** Let $\mathcal{E}$ be bootstrappable with respect to $\Gamma$.

1. For every $d$, the scheme $\mathcal{E}^{(d)}$, which uses $d + 1$ key pairs of $\mathcal{E}$ with each secret key encrypted bit by bit under the next public key, compactly
   evaluates all circuits of depth at most $d$ with gates in $\Gamma$; if $\Gamma$ is universal, the family $\mathcal{E}^{(d)}$ is leveled fully homomorphic.
2. An algorithm that $(t, \varepsilon)$-breaks the semantic security of $\mathcal{E}^{(d)}$ yields one that $(t', \varepsilon')$-breaks that of $\mathcal{E}$ with $t' \approx t \cdot \ell$ and
   $\varepsilon' \ge \varepsilon / (\ell(d + 1))$, where $\ell$ is the number of plaintext symbols in a secret key.
3. If $\mathcal{E}$ is moreover KDM-secure and bootstrappable with respect to a universal set of gates, the scheme $\mathcal{E}^*$ obtained with a single key pair and an
   encryption of the secret key under its own public key is semantically secure and fully homomorphic.

## Proof depends on

- [The hybrid step](../../security-games/games-and-advantages/advantage-hybrid-uniform.md)

## Expansion

This page becomes ready once:

- The exact running-time overhead $t'$ of the reduction in part 2, as a function of $t$, $\ell$, $d$ and the cost of encryption, in place of $t' \approx t \cdot \ell$ (statement prerequisite; not yet stated)
- Key-dependent-message (KDM) security for encryption of the scheme's own secret key, used in part 3 (statement prerequisite; not yet stated)

## Sources

- C. Gentry, *A fully homomorphic encryption scheme*, PhD thesis, Stanford University, 2009, <https://crypto.stanford.edu/craig/craig-thesis.pdf>: Section 4.1 (Definitions 4.1.2 and 4.1.3), Section 4.2 (the construction of $\mathcal{E}^{(d)}$, Theorems 4.2.1–4.2.3) and Section 4.3 (Theorem 4.3.2).
