# Supersingular elliptic curves and isogenies

Let $p$ be a prime and consider supersingular elliptic curves over $\overline{\mathbb{F}}_p$, as defined on the page listed under Depends on. Every supersingular curve is isomorphic over $\overline{\mathbb{F}}_p$ to one defined over $\mathbb{F}_{p^{2}}$, and there are $\lfloor p/12\rfloor+\epsilon$ supersingular $j$-invariants with $\epsilon\in\{0,1,2\}$. An *isogeny* $\varphi:E\to E'$ is a non-constant morphism with $\varphi(O)=O$; it is a group homomorphism, its degree $\deg\varphi$ equals $|\ker\varphi|$ when separable, and it has a *dual* $\hat{\varphi}:E'\to E$ with $\hat{\varphi}\varphi=[\deg\varphi]$. For every finite subgroup $G\subseteq E$ there is a separable isogeny with kernel $G$, unique up to isomorphism of the codomain, computable by Vélu's formulas in time polynomial in $|G|$.

## Depends on

- [Supersingular elliptic curves](../../../../../AlgebraicGeometry/elliptic-curves/supersingular-elliptic-curves/is-supersingular.md)

## Sources

- Jacques Vélu, "Isogénies entre courbes elliptiques", Comptes Rendus de l'Académie des Sciences de Paris (1971).
- David Jao, Luca De Feo, "Towards Quantum-Resistant Cryptosystems from Supersingular Elliptic Curve Isogenies", PQCrypto (2011).
- Luca De Feo, David Kohel, Antonin Leroux, Christophe Petit, Benjamin Wesolowski, "SQISign: Compact Post-Quantum Signatures from Quaternions and Isogenies", ASIACRYPT (2020), IACR ePrint 2020/1240.
