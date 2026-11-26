# Deferring the linear-time check of inner-product arguments

Let $\mathsf{PC}_{\mathrm{DL}}$ be the inner-product-argument polynomial commitment over a prime-order group $\mathbb{G}$ (order $q$) with Pedersen generators $G_0,\dots,G_d$, where $d+1=2^{k}$. For an evaluation claim with proof $\pi$, the *succinct check* recomputes the challenges $\xi_0,\xi_1,\dots,\xi_k\in\mathbb{F}_q$ from the random oracle, uses $O(k)$ scalar multiplications to check every equation except one, and outputs the polynomial

$$
h(X)=\prod_{i=0}^{k-1}\bigl(1+\xi_{k-i}\,X^{2^{i}}\bigr)\in\mathbb{F}_q[X],
$$

whose constant term is $1$, together with the group element $U$ contained in $\pi$. The full check additionally verifies that $U$ is the commitment to the coefficient vector of $h$, which takes $O(d)$ scalar multiplications; $h(z)$ itself can be evaluated with $O(k)$ field operations. Claims of the form "$U_i$ commits to $h_i$" can be accumulated: with $\alpha$ and then $z$ derived from the random oracle, set $h=\sum_i\alpha^{i}h_i$ and $C=\sum_i\alpha^{i}U_i$; the accumulation prover supplies an evaluation proof that $C$ opens to $v=h(z)$ at $z$, forming the new accumulator; the accumulation verifier recomputes $C$, $z$ and checks $h(z)=v$ with $O(\log d)$ scalar multiplications per claim; and the decider runs the full check of that one evaluation proof, with $O(d)$ scalar multiplications.

## Proof sketch

Unrolling the folding of the generators shows that the final generator $U$ is $\sum_i s_iG_i$ with $s_i$ a product of challenges selected by the binary expansion of $i$, which is the coefficient vector of $h$. Since commitments are linear in coefficients, $C$ commits to $h$ whenever every $U_i$ commits to $h_i$. Conversely, if some $U_i$ does not, then $\sum_i\alpha^{i}(U_i-\mathsf{Commit}(h_i))=0$ only for few $\alpha$, and if $C$ does not commit to $h$, an accepted opening at the random-oracle point $z$ to $h(z)$ is unlikely by the extractability of $\mathsf{PC}_{\mathrm{DL}}$; both events reduce to zero-finding games in the random oracle model.

## Depends on

- [Accumulation scheme for a predicate](accumulation-scheme.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Pedersen commitment scheme](../commitment-schemes/pedersen-commitments-perfect-hiding-and-binding/scheme.md)
- [The random oracle model](../../public-key/random-oracle-constructions/the-random-oracle-model.md)

## Sources

- Benedikt Bünz, Alessandro Chiesa, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data from Accumulation Schemes", TCC (2020), IACR ePrint 2020/499, Section 7.1 and Appendix A (Figure 2, the subroutine $\mathsf{PC}_{\mathrm{DL}}.\mathsf{SuccinctCheck}$).
