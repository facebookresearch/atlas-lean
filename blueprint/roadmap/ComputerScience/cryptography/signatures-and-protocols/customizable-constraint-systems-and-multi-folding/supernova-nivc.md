# NIVC from multi-folding with one running instance per function

Let $\mathsf{NIFS}$ be an NIVC-compatible non-interactive multi-folding scheme for a relation $\mathcal{R}_1$ and a committed relation $\mathcal{R}_2$, with a default pair $(u_\perp,w_\perp)\in\mathcal{R}_1$ (for example the CCS multi-folding scheme with $\mathcal{R}_1$ the LCCCS relation and $\mathcal{R}_2$ the CCCS relation; the construction assumes such a non-interactive scheme in the plain model, which is instantiated heuristically by applying Fiat–Shamir with a concrete hash to the public-coin scheme), and let $\mathsf{hash}$ be a hash function. For functions $F_1,\dots,F_\ell$ and a control function $\varphi$, define for each $j$ the augmented function $F'_j$, which takes all inputs as advice: it computes $\mathrm{pc}_{i+1}=\varphi(z_i,\omega_i)$ and $z_{i+1}=F_j(z_i,\omega_i)$; if $i=0$ it checks $z_i=z_0$ and sets the list of running instances to $\mathbf{U}_1=(u_\perp,\dots,u_\perp)$; otherwise it checks that the public part of the fresh committed instance $u_i$ equals the encoding of $\mathsf{hash}(\mathsf{vk},i,z_0,z_i,\mathbf{U}_i,\mathrm{pc}_i)$, checks $1\le\mathrm{pc}_i\le\ell$, and replaces only the entry $\mathbf{U}_i[\mathrm{pc}_i]$ by the folding verifier's output on $(\mathbf{U}_i[\mathrm{pc}_i],u_i)$; it outputs $\mathsf{hash}(\mathsf{vk},i+1,z_0,z_{i+1},\mathbf{U}_{i+1},\mathrm{pc}_{i+1})$. A proof for $(i,z_0,z_i)$ is $\Pi_i=((\mathbf{U}_i,\mathbf{W}_i),(u_i,w_i),\mathrm{pc}_i)$: the $\ell$ running instance-witness pairs, one per function, the latest fresh committed instance-witness pair, attesting to the execution of $F'_{\mathrm{pc}_i}$, and the program counter. The verifier accepts $i=0$ iff $z_i=z_0$; otherwise it checks the hash in $u_i$, checks $1\le\mathrm{pc}_i\le\ell$, checks every $(\mathbf{U}_i[j],\mathbf{W}_i[j])\in\mathcal{R}_1$ and checks $(u_i,w_i)\in\mathcal{R}_2$ for the structure of $F'_{\mathrm{pc}_i}$. This is an NIVC scheme. Instantiated with the CCS multi-folding scheme and Pedersen commitments, the prover's step for $F_j$ costs one multi-scalar multiplication of size $O(n_\varphi+n_j)$ plus field operations depending only on the CCS sizes of $F_j$ and $\varphi$; with the running instances kept in externalized memory, the recursive circuit performs one group scalar multiplication, $O(d\log m_j)$ field operations, $O(\log m_j)$ random-oracle calls, one evaluation of $\varphi$, two hashes and two memory operations over the $\ell$ running instances. The proof itself is linear in the sizes of the circuits of all $\ell$ functions; making it zero-knowledge or succinct needs a separate layer.

## Proof sketch

Completeness follows by induction on $i$, the base case using the default instances. For knowledge soundness, from a prover producing an accepted $\Pi_i$ the extractor of the folding scheme yields $\Pi_{i-1}$ and $\omega_{i-1}$: the hash in $u_i$ binds the previous running list, counter and state, and the extracted witness for $u_i$ shows that $F'_{\mathrm{pc}_i}$ ran correctly. This gives a prover for $i-1$ steps, and repeating the step recovers all advice values.

## Depends on

- [Non-uniform incrementally verifiable computation](non-uniform-ivc.md)
- [Folding scheme for an NP relation](../relaxed-r1cs-folding-schemes/folding-scheme.md)
- [Linearized committed CCS instances](linearized-committed-ccs.md)

## Proof depends on

- [HyperNova multi-folding scheme for CCS](hypernova-multifolding.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573, Section 6 (Definition 12, Construction 2, Lemma 4, Theorem 3) and Section 7.
