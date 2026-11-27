# Micciancio–Peikert $G$-trapdoors and tagged parity-check matrices

Let $q = 2^w$, $\bar A \in \mathbb{Z}_q^{\ell \times \bar m}$, and let $G \in \mathbb{Z}_q^{\ell \times \ell w}$ be the gadget matrix. For an invertible *tag* $H \in \mathbb{Z}_q^{\ell \times \ell}$, an integer matrix $R \in \mathbb{Z}^{\bar m \times \ell w}$ is a *$G$-trapdoor with tag $H$* for $A \in \mathbb{Z}_q^{\ell \times (\bar m + \ell w)}$ if

$$
A \begin{pmatrix} R \\ I \end{pmatrix} \equiv H G \pmod q .
$$

The trapdoor-generation algorithm samples $\bar A$ uniform and $R$ with small entries and outputs the *tagged matrix* $A = [\,\bar A \mid HG - \bar A R\,]$, for which $R$ is a $G$-trapdoor with tag $H$. The *quality* of the trapdoor is the largest singular value $s_1(R)$ of $R$ (Micciancio and Peikert, Definition 5.2). If the entries of $R$ are independent, each equal to $0$ with probability $1/2$ and to $1$ and $-1$ with probability $1/4$ each, then $(\bar A, \bar A R)$ is within statistical distance $\tfrac{\ell w}{2}\sqrt{q^{\ell}/2^{\bar m}}$ of uniform by a version of the leftover hash lemma (Section 5.2), and hence so is $A$, which is obtained from $(\bar A, -\bar A R)$ by adding the fixed matrix $HG$ to its second block.

## Depends on

- [The binary gadget vector and gadget matrix](gadget-matrix.md)
- [The short integer solution problem (SIS)](../lattice-problems/short-integer-solution-problem.md)

## Sources

- Daniele Micciancio and Chris Peikert, "Trapdoors for Lattices: Simpler, Tighter, Faster, Smaller", Advances in Cryptology – EUROCRYPT 2012, 2012, Definition 5.2 and Section 5.2 (statistical instantiation).
