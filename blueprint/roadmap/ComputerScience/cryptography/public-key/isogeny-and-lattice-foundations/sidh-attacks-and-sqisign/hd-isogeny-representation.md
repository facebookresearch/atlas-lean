# Higher-dimensional representations of isogenies of arbitrary degree

Let $\varphi:E\to E'$ be an isogeny of degree $d$ and $N> d$ an integer such that $N-d$ is a sum of at most four squares, and suppose the action of $\varphi$ on $E[N]$ is known. Then there is an $N$-isogeny $F$ between products of at most $8$ elliptic curves (dimension $\le 8$, often $2$ or $4$) having $\varphi$ as a block, whose kernel is computable from $\varphi|_{E[N]}$; for $N=2^{e}$, $F$ is a chain of $(2,\dots,2)$-isogenies computable in time polynomial in $e$. Hence $\varphi$ can be represented by $(E,E',\varphi|_{E[2^{e}]})$ and evaluated on any point in polynomial time, regardless of the factorization of $d$.

## Proof sketch

Write $N-d=a_1^{2}+\dots+a_4^{2}$ and let $\alpha$ be the endomorphism of $E^{4}$ given by the quaternion matrix of $(a_1,\dots,a_4)$, of degree $N-d$ per coordinate (Zarhin's trick). Apply Kani's lemma to the diamond formed by $\varphi^{\times 4}$ and $\alpha$ on $E^{4}$, giving an $N$-isogeny on $E^{4}\times E'^{4}$. Evaluating the chain at $(P,0,\dots,0)$ yields $\varphi(P)$ in a coordinate.

## Depends on

- [Supersingular elliptic curves and isogenies](../supersingular-isogenies-and-quaternion-orders/supersingular-curves.md)

## Proof depends on

- [Kani's lemma: isogeny diamonds give isogenies of abelian surfaces](kani-criterion.md)

## Sources

- Damien Robert, "Breaking SIDH in Polynomial Time", EUROCRYPT (2023), IACR ePrint 2022/1038.
- Pierrick Dartois, Antonin Leroux, Damien Robert, Benjamin Wesolowski, "SQIsignHD: New Dimensions in Cryptography", EUROCRYPT (2024), IACR ePrint 2023/436.
