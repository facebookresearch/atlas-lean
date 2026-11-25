# Security of KZG polynomial commitments

Let $(\mathbb{G}, \mathbb{G}_T, e)$ be a symmetric bilinear group of prime order $p$ with generator $g$, and let the reference string be $(g, g^\alpha, \dots, g^{\alpha^t})$ for a secret $\alpha$ that is erased. In the scheme PolyCommit$_{\mathrm{DL}}$, the commitment to $\phi \in \mathbb{Z}_p[x]$ of degree at most $t$ is $C = g^{\phi(\alpha)}$; the witness for the evaluation $\phi(i)$ is $w = g^{\psi(\alpha)}$ with $\psi(x) = (\phi(x) - \phi(i))/(x - i)$; and the verifier checks $e(C, g) = e(w, g^{\alpha}/g^{i})\, e(g, g)^{\phi(i)}$. The scheme is correct; it is evaluation binding (no efficient adversary outputs a commitment and accepting witnesses for two different values at the same point) under the $t$-strong Diffie–Hellman assumption; and it is polynomial binding under the $t$-strong Diffie–Hellman assumption, since two polynomials with equal commitments give a nonzero polynomial with root $\alpha$. It is hiding in the following sense, under the discrete logarithm assumption: for $\phi$ chosen uniformly at random among polynomials of degree $t$, no efficient adversary given the reference string, $C$ and $t$ evaluations $\phi(i_1), \dots, \phi(i_t)$ with accepting witnesses can compute $\phi(\hat\jmath)$ with non-negligible probability at any index $\hat\jmath$ outside $\{i_1, \dots, i_t\}$. Commitments are deterministic, so commitments to fixed polynomials are distinguishable (the constant polynomials $0$ and $1$ commit to the identity and to $g$); hiding of arbitrary polynomials requires the randomized variant PolyCommit$_{\mathrm{Ped}}$.

## Depends on

- [Polynomial commitment schemes](polynomial-commitment-schemes.md)
- [Pairing-based assumptions: BDH and t-SDH](../../public-key/advanced-encryption-and-pairings/pairing-based-assumptions-bdh-and-t-sdh.md)
- [Discrete-logarithm experiment](../../public-key/hardness-assumptions/dlog-game.md)

## Sources

- A. Kate, G. M. Zaverucha and I. Goldberg, "Constant-size commitments to polynomials and their applications", *ASIACRYPT 2010*, LNCS 6477, Springer, 2010; technical report CACR 2010-10, <https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf>, Theorem 3.2
