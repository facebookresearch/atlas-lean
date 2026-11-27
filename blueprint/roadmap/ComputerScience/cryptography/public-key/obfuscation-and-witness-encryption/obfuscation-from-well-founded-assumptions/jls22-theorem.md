# Indistinguishability obfuscation without lattices: LPN over F_p, DLIN and local PRGs

Let $(\mathbb{G},\mathbb{G}_T,e,g,p)$ be a symmetric bilinear group of prime order $p$. The *decisional linear (DLIN) assumption* states that for uniform $a,b,x,y,z\in\mathbb{Z}_p$ the tuples $(g,g^{a},g^{b},g^{ax},g^{by},g^{x+y})$ and $(g,g^{a},g^{b},g^{ax},g^{by},g^{z})$ are computationally indistinguishable given the group description. Assume sub-exponential security of: LPN over $\mathbb{Z}_p$ with polynomially many samples and error rate $\ell^{-\delta}$, where $\ell$ is the dimension of the secret and $\delta>0$ is any constant; the existence of a Boolean PRG in $\mathsf{NC}^{0}$ with stretch $n^{1+\tau}$ for a constant $\tau>0$; and DLIN in symmetric bilinear groups of prime order. Then (sub-exponentially secure) indistinguishability obfuscation for all polynomial-size circuits exists; assuming only polynomial security of these assumptions, collusion-resistant public-key functional encryption for all polynomial-size circuits exists. In particular the LWE assumption can be removed from the well-founded-assumptions route to iO.

## Proof sketch

The construction introduces preprocessed randomized encodings: the input and random coins are preprocessed, in time sublinear in the size of the circuit, into a public part and a private part, so that a randomized encoding of the computation is given by polynomials of constant degree in the public part and degree $2$ in the private part, over $\mathbb{F}_p$; LPN over $\mathbb{F}_p$ and the $\mathsf{NC}^{0}$ PRG provide this. Evaluating these polynomials with a partially hiding functional encryption scheme based on DLIN gives public-key functional encryption for circuits with encryption time sublinear in the circuit size, and FE-to-iO bootstrapping gives iO.

## Depends on

- [Learning parity with noise over large prime fields with sparse errors](lpn-over-large-fields.md)
- [Pseudorandom generators in NC0 with polynomial stretch](local-prg.md)
- [Bilinear groups](../../advanced-encryption-and-pairings/bilinear-groups.md)
- [Indistinguishability and virtual black-box obfuscation](../../../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Indistinguishability obfuscation from sub-exponentially secure compact functional encryption](../compact-functional-encryption-to-obfuscation/fe-to-io-bootstrapping.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from LPN over F_p, DLIN, and PRGs in NC^0", EUROCRYPT (2022), IACR ePrint 2021/1334, abstract and Theorem 1.1.
- Dan Boneh, Xavier Boyen, Hovav Shacham, "Short Group Signatures", CRYPTO (2004) (the decisional linear assumption).
