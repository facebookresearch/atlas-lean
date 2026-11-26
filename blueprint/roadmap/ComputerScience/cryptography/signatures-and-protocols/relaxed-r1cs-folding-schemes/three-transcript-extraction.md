# Interpolation extractor from three folding transcripts

Let $\mathbb{F}$ be a field and suppose that for three distinct challenges $r_1,r_2,r_3\in\mathbb{F}$ the folding prover returns $(W^{(j)},E^{(j)})$ satisfying $W^{(j)}=W_1+r_jW_2$ and $E^{(j)}=E_1+r_jT+r_j^{2}E_2$ for unknown vectors $W_1,W_2,E_1,T,E_2$. Then these unknowns are uniquely determined and computable in time linear in their length: $W_1,W_2$ by solving the $2\times 2$ Vandermonde system from any two transcripts, and $E_1,T,E_2$ by inverting the $3\times 3$ Vandermonde matrix $(r_j^{k})_{j,k}$, which is invertible because the $r_j$ are distinct. Moreover, if each folded pair satisfies the relaxed relation, then so do $(E_1,u_1,x_1;W_1)$ and $(E_2,u_2,x_2;W_2)$.

## Proof sketch

The Vandermonde determinant $\prod_{j< k}(r_k-r_j)$ is nonzero. For the final claim, $g(r)=Az\circ Bz-uCz-E$ with $z=z_1+rz_2$ is a vector of polynomials of degree at most $2$ in $r$ vanishing at three distinct points, hence identically zero; its constant and leading coefficients are the residuals of the two input instances.

## Depends on

- [Relaxed R1CS instances with slack vector and scalar](relaxed-r1cs.md)

## Proof depends on

- [Cross-term identity for folding relaxed R1CS](nova-cross-term.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370.
