# Indistinguishability versus simulation privacy of garbling schemes

For a garbling scheme $\mathcal{G}$ with side information $\Phi$: (i) prv.sim security implies prv.ind security, and for every prv.ind adversary $\mathcal{A}$ there is a prv.sim adversary $\mathcal{B}$ with $\mathrm{Adv}^{\mathrm{prv.ind}}(\mathcal{A}) \le 2\,\mathrm{Adv}^{\mathrm{prv.sim}}(\mathcal{B}, \mathcal{S})$ for every simulator $\mathcal{S}$; (ii) if $(\Phi, \mathrm{ev})$ is *efficiently invertible* — there is a polynomial-time algorithm that, given $\phi$ and $y$, outputs $(f, x)$ with $\Phi(f) = \phi$ and $\mathrm{ev}(f, x) = y$ — then prv.ind security implies prv.sim security, with the simulator that inverts and garbles honestly. The side-information functions $\Phi_{\mathrm{topo}}$ and $\Phi_{\mathrm{size}}$ on conventional Boolean circuits are efficiently invertible (by a circuit that hardwires the output through constant gates on the given topology). The same relations hold for obliviousness. Moreover, adaptive prv1 simulation security implies selective prv.sim security with exact advantage preservation, and a universal simulator (one simulator for all adversaries) gives the per-adversary notion.

## Proof sketch

(i) Both worlds of the ind game are within the sim advantage of the same simulated world. (ii) Given $\phi$ and $y$, the inverter produces a pair $(f', x')$ consistent with them; garbling $(f', x')$ is indistinguishable from garbling the adversary's pair by prv.ind.

## Depends on

- [Side-information functions and privacy notions for garbling schemes](garbling-privacy-notions.md)

## Sources

- Mihir Bellare, Viet Tung Hoang and Phillip Rogaway, "Foundations of Garbled Circuits", Proceedings of the 2012 ACM Conference on Computer and Communications Security, 2012.
