# Relaxed R1CS instances with slack vector and scalar

For an R1CS structure $(m,n,\ell,A,B,C)$, a *relaxed R1CS instance* is a triple $(E,u,x)$ with error vector $E\in\mathbb{F}^{m}$, scalar $u\in\mathbb{F}$ and public input $x\in\mathbb{F}^{\ell}$; a witness $W$ satisfies it iff, with $z=(W,u,x)$,

$$
(Az)\circ(Bz)=u\cdot(Cz)+E.
$$

Every R1CS instance $x$ with witness $W$ is the relaxed instance $(0,1,x)$. A *committed relaxed R1CS instance* is $(\overline{E},u,\overline{W},x)$ where $\overline{E}=\mathsf{Com}(pp,E,r_E)$ and $\overline{W}=\mathsf{Com}(pp,W,r_W)$ for an additively homomorphic commitment scheme; a witness is $(E,r_E,W,r_W)$ opening both commitments and satisfying the relaxed relation.

## Depends on

- [Rank-1 constraint systems](rank-one-constraint-system.md)
- [Pedersen commitment scheme](../commitment-schemes/pedersen-commitments-perfect-hiding-and-binding/scheme.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, Ioanna Tzialla, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes", CRYPTO (2022), IACR ePrint 2021/370.
