# Accumulation for any additively homomorphic polynomial commitment

Let $\mathsf{PC}$ be a polynomial commitment scheme whose commitments lie in a group and are additively homomorphic, $\mathsf{Com}(f)+\mathsf{Com}(g)=\mathsf{Com}(f+g)$ and $\alpha\cdot\mathsf{Com}(f)=\mathsf{Com}(\alpha f)$, and which is evaluation-binding. Then the predicate "$C$ opens to a polynomial $f$ of degree $< d$ with $f(z)=v$" has a (private) accumulation scheme whose verifier performs $O(m)$ group operations to accumulate $m$ claims, by reducing claims at distinct points to a single claim at a fresh random point via quotient polynomials and random linear combinations. As a result, PCD can be built from any such commitment, including group-of-unknown-order commitments.

## Proof sketch

Given claims $(C_i,z_i,v_i)$, the prover commits to $q_i(X)=(f_i(X)-v_i)/(X-z_i)$; a random challenge $r$ lets the verifier reduce all claims to evaluating the linear combination $\sum_i\alpha^{i}C_i$ at $r$, using homomorphism. If some claim is false, the corresponding quotient is not a polynomial, and a random evaluation detects the inconsistency except with probability $O(d/|\mathbb{F}|)$; evaluation binding converts a successful cheat into an attack.

## Depends on

- [Accumulation scheme for a predicate](accumulation-scheme.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Proof-carrying data for a compliance predicate](pcd-scheme.md)

## Sources

- Dan Boneh, Justin Drake, Ben Fisch, Ariel Gabizon, "Halo Infinite: Proof-Carrying Data from Additive Polynomial Commitments", CRYPTO (2021), IACR ePrint 2020/1536.
