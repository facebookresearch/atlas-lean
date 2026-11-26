# Deferring the linear-time check of inner-product arguments

In the inner-product-argument polynomial commitment over a group $\mathbb{G}$ with generators $G_0,\dots,G_{d-1}$ ($d=2^{k}$), after $k$ folding rounds with challenges $u_1,\dots,u_k\in\mathbb{F}^{\times}$ the verifier must check one equation involving $G'=\langle\mathbf{s},\mathbf{G}\rangle$, where $\mathbf{s}$ is the coefficient vector of
$h(X)=\prod_{i=1}^{k}\bigl(u_i^{-1}+u_i X^{2^{i-1}}\bigr)$. All other verifier work is $O(k)$ group operations, and $h(z)$ can be evaluated in $O(k)$ field operations for any $z$. Hence the only linear-time check is "$G'$ is a commitment to $h$", an instance of a polynomial-evaluation claim that can be accumulated: given claims $(G'_j,h_j)$, a random point $z$ and a random linear combination reduce them to a single opening of $\sum_j\alpha^{j}G'_j$ at $z$.

## Proof sketch

Unrolling the folding recursion shows that the final generator is $\sum_i s_iG_i$ with $s_i=\prod_{\ell}u_\ell^{\pm1}$ determined by the binary expansion of $i$, which is exactly the coefficient vector of the product $h(X)$. Evaluating $h$ is a product of $k$ factors. Since commitments are linear in coefficients, several claims about the same generators combine linearly, and a polynomial identity checked at a random $z$ has soundness error at most $d/|\mathbb{F}|$ by Schwartz–Zippel.

## Depends on

- [Accumulation scheme for a predicate](accumulation-scheme.md)
- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)
- [Pedersen commitment scheme](../commitment-schemes/pedersen-commitments-perfect-hiding-and-binding/scheme.md)

## Proof depends on

- [Polynomial commitment schemes](../zero-knowledge-and-arguments/polynomial-commitment-schemes.md)

## Sources

- Sean Bowe, Jack Grigg, Daira Hopwood, "Recursive Proof Composition without a Trusted Setup", IACR ePrint 2019/1021 (2019).
- Benedikt Bünz, Alessandro Chiesa, Pratyush Mishra, Nicholas Spooner, "Proof-Carrying Data from Accumulation Schemes", TCC (2020), IACR ePrint 2020/499.
