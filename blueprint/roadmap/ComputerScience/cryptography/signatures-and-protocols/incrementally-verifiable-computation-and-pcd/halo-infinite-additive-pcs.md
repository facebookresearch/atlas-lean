# Accumulation for any additively homomorphic polynomial commitment

Let $\mathsf{PC}$ be a polynomial commitment scheme for polynomials in $\mathbb{F}_p^{(<d)}[X]$ whose commitments lie in an abelian group of size at most $2^{\mathrm{poly}(\lambda)}$ and are additive, $\mathsf{Com}(f)+\mathsf{Com}(g)=\mathsf{Com}(f+g)$, and whose evaluation protocol is a knowledge-sound proof. Then $\mathsf{PC}$ has a (private) aggregation scheme: a public-coin protocol that turns $\ell$ evaluation claims $(C_i,z_i,v_i)$, with openings known to the prover, into one claim $(C^{*},r,0)$ whose evaluation proof the prover can produce, such that the protocol followed by the evaluation proof of the output claim is a proof of knowledge of openings of all $C_i$ with $f_i(z_i)=v_i$. The verifier performs $O(\ell\log\ell)$ field operations and $O(\ell\lambda)$ group operations, a single linear combination of $\ell+2$ commitments with $\lambda$-bit integer coefficients, the prover additionally commits to one polynomial, and the communication is one group element and two field elements. A public aggregation scheme for a succinct additive commitment satisfies the definition of a PCS accumulation scheme, and combined with a SNARK whose verifier is efficient given an oracle for the evaluation checks it yields PCD only heuristically: such SNARKs are known in the random oracle model, and the compiler to PCD requires instantiating that oracle with a concrete hash function.

## Proof sketch

Let $\Omega=\{z_1,\dots,z_\ell\}$, $Z(X)=\prod_{\omega\in\Omega}(X-\omega)$ and $Z_i(X)=\prod_{\omega\in\Omega\setminus\{z_i\}}(X-\omega)$. After the verifier sends $\rho$, the prover commits to the single quotient $q=\sum_i\rho^{i-1}Z_i\,(f_i-v_i)/Z$, which is a polynomial when every claim holds; after the verifier sends $r$, both sides form $C_g=\sum_i\rho^{i-1}Z_i(r)\,(C_i-v_i\cdot\mathsf{Com}(1))-Z(r)\,C_q$, and the output claim is that $C_g$ opens to a polynomial vanishing at $r$. For distinct points and $r\notin\Omega$, this check is $\sum_i\rho^{i-1}Z(r)\bigl((f_i(r)-v_i)/(r-z_i)-q_i(r)\bigr)=0$ with $q=\sum_i\rho^{i-1}q_i$: a $\rho$-combination of the identities $f_i(r)-v_i=(r-z_i)q_i(r)$, so the quotient commitment, not only a combination of the original commitments, is what the evaluation tests. Knowledge soundness rewinds over $\rho$ and $r$ and uses the invertibility of a random Vandermonde matrix multiplied entrywise by a matrix of nonzero entries.

## Depends on

- [Accumulation scheme for a predicate](accumulation-scheme.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Proof-carrying data for a compliance predicate](pcd-scheme.md)

## Sources

- Dan Boneh, Justin Drake, Ben Fisch, Ariel Gabizon, "Halo Infinite: Proof-Carrying Data from Additive Polynomial Commitments", CRYPTO (2021), IACR ePrint 2020/1536, Definitions 6 and 10, Figure 2, Theorems 3 to 5, Corollary 1 and Section 6.
