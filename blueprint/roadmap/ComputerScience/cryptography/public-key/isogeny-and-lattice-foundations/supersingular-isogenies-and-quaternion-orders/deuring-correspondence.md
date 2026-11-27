# The Deuring correspondence between supersingular curves and maximal orders

For every supersingular elliptic curve $E/\overline{\mathbb{F}}_p$, the endomorphism ring $\mathrm{End}(E)$ is isomorphic to a maximal order in $B_{p,\infty}$. The map $E\mapsto\mathrm{End}(E)$ induces a bijection between supersingular $j$-invariants up to Galois conjugation $j\mapsto j^{p}$ and isomorphism classes (types) of maximal orders in $B_{p,\infty}$. Moreover, fixing $E_0$ with $\mathcal{O}_0=\mathrm{End}(E_0)$, each separable isogeny $\varphi:E_0\to E$ corresponds to the left $\mathcal{O}_0$-ideal $I_\varphi=\{\alpha\in\mathcal{O}_0:\alpha(\ker\varphi)=0\}$, with $\mathrm{nrd}(I_\varphi)=\deg\varphi$ and $\mathcal{O}_R(I_\varphi)\cong\mathrm{End}(E)$; conversely $\ker\varphi_I=\bigcap_{\alpha\in I}\ker\alpha$. Equivalent ideals correspond to isogenies with isomorphic codomains, and composition corresponds to ideal multiplication.

## Proof sketch

Deuring showed that endomorphism rings of supersingular curves are maximal orders in the quaternion algebra ramified at $p$ and $\infty$ and that every type arises, with the class number of $B_{p,\infty}$ matching the count of supersingular $j$-invariants up to conjugation. The kernel–ideal dictionary follows from the action of $\mathcal{O}_0$ on torsion points and the fact that the left ideal annihilating a subgroup has norm equal to its order.

## Depends on

- [Supersingular elliptic curves and isogenies](supersingular-curves.md)
- [The quaternion algebra ramified at p and infinity and its maximal orders](quaternion-algebra-bp.md)

## Sources

- Max Deuring, "Die Typen der Multiplikatorenringe elliptischer Funktionenkörper", Abhandlungen aus dem Mathematischen Seminar der Universität Hamburg 14 (1941).
- David Kohel, Kristin Lauter, Christophe Petit, Jean-Pierre Tignol, "On the Quaternion l-Isogeny Path Problem", LMS Journal of Computation and Mathematics 17A (2014), arXiv:1406.0981.
- Luca De Feo, David Kohel, Antonin Leroux, Christophe Petit, Benjamin Wesolowski, "SQISign: Compact Post-Quantum Signatures from Quaternions and Isogenies", ASIACRYPT (2020), IACR ePrint 2020/1240.
