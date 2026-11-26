# Bootstrapping gives leveled fully homomorphic encryption

Let $\mathcal{E}$ be an IND-CPA secure bit-encryption scheme that is bootstrappable for the identity and NAND gates, whose decryption circuits are generated uniformly in polynomial time, and let $B(\lambda)$ be a polynomially bounded depth budget. The *leveled scheme* $\mathcal{E}^{(B)}$ generates $B + 1$ base key pairs $(sk_i, pk_i)$, $0 \le i \le B$, and the acyclic chain of encryptions of the bits of $sk_i$ under $pk_{i-1}$ for $1 \le i \le B$, encrypts under $pk_B$, evaluates any circuit of identity and NAND gates of depth at most $B$ level by level (adding identity gates so that every wire joins consecutive levels; a Boolean circuit of depth $d$ compiles into such a circuit of depth $2d$), recrypting the ciphertexts of each level under the next key of the chain, and decrypts with $sk_0$. Let $\ell_{sk}$ be the bit length of a formatted base secret key. Then (Gentry's thesis, Theorems 4.2.1, 4.2.2 and 4.2.3): (i) $\mathcal{E}^{(B)}$ correctly evaluates every such circuit of depth at most $B$; (ii) it is compact: evaluated ciphertexts are base ciphertexts under $pk_0$, so decryption is computed by a polynomial-size circuit on ciphertexts whose width does not depend on $B$ or on the evaluated circuit, and evaluating a circuit of size $s$ costs at most $s\,\ell_{sk} B$ base encryptions and $s B$ base evaluations of augmented decryption circuits; (iii) it is IND-CPA secure: an adversary that breaks $\mathcal{E}^{(B)}$ in time $t$ with advantage $\epsilon$ yields an adversary that breaks $\mathcal{E}$ in time about $t\,\ell_{sk}$ with advantage at least $\epsilon / (\ell_{sk}(B + 1))$, that is,

$$
\mathrm{Adv}_{\mathcal{E}^{(B)}}(\mathcal{A}) \le \ell_{sk}\,(B + 1)\cdot \mathrm{Adv}_{\mathcal{E}}(\mathcal{B}).
$$

All schemes $\{\mathcal{E}^{(d)}\}_{d}$ run in one uniform polynomial time bound in $\lambda$ and $d$.

## Proof sketch

Correctness is the layered-evaluation lemma: augmenting a level with decryption circuits preserves wire values by correctness of recryption, and reducing it preserves them by correctness of evaluation on augmented decryption circuits. Compactness holds because evaluated ciphertexts are base ciphertexts under the last key. Security: in Game $k$, for $0 \le k \le B$, the encrypted key bits of the first $k$ links are replaced by encryptions of the bits of unrelated fresh keys (the key-chain theorem), and in Game $B + 1$ the challenge encrypts a random plaintext, so the adversary has no advantage. Some consecutive pair of the $B + 2$ games differs by at least $\epsilon/(B+1)$, and that gap is a break of the $\ell_{sk}$-fold concatenation of $\mathcal{E}$, which costs the factor $\ell_{sk}$.

## Depends on

- [Gentry's bootstrapping theorem](../gentry-s-bootstrapping-theorem.md)
- [Homomorphic encryption: correctness and compactness](../homomorphic-encryption-correctness-and.md)
- [CPA security of public-key encryption families](../../../security-games/asymptotic-security/pub-cpasecure.md)

## Proof depends on

- [Homomorphic evaluation of Boolean circuits layer by layer along a key chain](layered-circuit-evaluation.md)
- [Security of an acyclic encrypted-key chain](key-chain-security.md)

## Sources

- Craig Gentry, "Fully Homomorphic Encryption Using Ideal Lattices", Proceedings of the Forty-First Annual ACM Symposium on Theory of Computing, 2009.
- Craig Gentry, "A Fully Homomorphic Encryption Scheme", 2009.
