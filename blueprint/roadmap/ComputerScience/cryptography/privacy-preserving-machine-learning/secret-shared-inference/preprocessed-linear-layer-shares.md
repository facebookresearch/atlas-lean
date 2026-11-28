# Query-independent preprocessing for secret-shared linear layers

For a linear layer $x\mapsto M_ix$ held by the server, client and server pick masks $r_i$ and $s_i$ before the client's query is known, and the client obtains $M_ir_i-s_i$ through linearly homomorphic encryption. Online the server, given $x_i-r_i$, computes $M_i(x_i-r_i)+s_i$, and the two then hold additive shares of $M_ix_i$ with no online encryption.

Following the source's notation, fix a finite ring $R$ and a width $n$ such that every layer's input and output are vectors in $R^n$ (narrower layers padded), so the server's weights for layer $i$ are a matrix $M_i\in R^{n\times n}$. The client owns a key pair $(pk,sk)$ of a public-key encryption scheme with plaintext space $R^n$ and a public evaluation algorithm $\mathrm{Eval}$ such that for every generated key pair, every $r\in R^n$, every ciphertext $c$ output by $\mathrm{Enc}(pk,r)$, every $M\in R^{n\times n}$ and every $s\in R^n$, $\mathrm{Dec}(sk,\mathrm{Eval}(pk,c,M,s))=Mr-s$ (the source's homomorphism condition, specialized to this affine map). *Preprocessing* (it uses $M_i$ but not the client's input): the client samples a fresh $r_i\leftarrow R^n$ and the server a fresh $s_i\leftarrow R^n$, uniformly; the client computes $c_i\leftarrow\mathrm{Enc}(pk,r_i)$ and sends $c_i$; the server returns $\mathrm{Eval}(pk,c_i,M_i,s_i)$; the client decrypts it and stores $M_ir_i-s_i$. *Online*, the server obtains $x_i-r_i$ (from the client for the first layer, from the previous non-linear layer's output protocol afterwards) and computes $M_i(x_i-r_i)+s_i$. Then

$$
\big(M_i(x_i-r_i)+s_i\big)+\big(M_ir_i-s_i\big)=M_ix_i .
$$

## Depends on

- [Homomorphic encryption scheme](../../public-key/homomorphic-encryption/scheme.md)
- [Additive $n$-out-of-$n$ secret sharing](../../signatures-and-protocols/secure-multiparty-computation/secret-sharing-schemes/additive-secret-sharing.md)

## Proof depends on

None.

## Expansion

A definition of the preprocessing and online linear step and its algebraic output. Not ready: a page for linearly homomorphic public-key encryption with this dimensioned affine evaluation is missing. Privacy of the step is not claimed here; Delphi's full protocol is shown to be a [secure inference protocol](../inference-security-models/secure-inference-functionality.md) in its Theorem 4.3, assuming garbled circuits, linearly homomorphic encryption and secure Beaver triple generation and multiplication, by the hybrid argument of Appendix B; Appendix A gives the formal definitions of these building blocks.

## Sources

- Pratyush Mishra, Ryan Lehmkuhl, Akshayaram Srinivasan, Wenting Zheng, Raluca Ada Popa, "Delphi: A Cryptographic Inference Service for Neural Networks", 29th USENIX Security Symposium (2020), §2.2, §§4.1–4.2, Figures 3–5, Theorem 4.3, Appendices A and B, [USENIX open-access copy](https://www.usenix.org/conference/usenixsecurity20/presentation/mishra).
