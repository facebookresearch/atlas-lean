# KLPT: ideals of powersmooth or prime-power norm in a special maximal order

Let $p\equiv 3\pmod 4$ and $\mathcal{O}_0=\mathbb{Z}\langle i,\frac{1+j}{2}\rangle$-type special maximal order of $B_{p,\infty}$ (containing $\mathbb{Z}[i]$ with $i^{2}=-1$). Fix a small prime $\ell$ (typically $2$ or $3$, or any constant prime). There is a probabilistic algorithm that, given a left $\mathcal{O}_0$-ideal $I$, outputs an equivalent left ideal $J=I\gamma$ of norm $\ell^{e}$ with $\ell^{e}\approx p^{7/2}$ (or, with minimal changes, of powersmooth norm), running in expected time polynomial in $\log p$ under heuristic assumptions on the distribution of represented primes. Kohel, Lauter, Petit and Tignol treat $\ell$ as a constant and solve this quaternion analogue of the $\ell$-isogeny path problem. Translating $J$ through the Deuring correspondence into a chain of $e$ isogenies of degree $\ell$ gives, for such small $\ell$, a heuristic polynomial-time path between curves whose endomorphism rings are known together with the action of their generators on the $\ell$-torsion (Eisenträger, Hallgren, Lauter, Morrison and Petit, Theorem 10).

## Proof sketch

First find an equivalent ideal of prime norm. Then solve norm equations of the form $\mathrm{nrd}(\gamma)=N(I)\ell^{e}$ in $\mathcal{O}_0$ using the special structure: solve $x^{2}+y^{2}+p(z^{2}+w^{2})=M$ by choosing $z,w$ to satisfy congruence conditions modulo $N(I)$ (strong approximation) and then representing the remainder as a sum of two squares via Cornacchia, which succeeds heuristically for many trials. The size $p^{7/2}$ arises from the lattice reductions and congruence conditions.

## Depends on

- [The quaternion algebra ramified at p and infinity and its maximal orders](quaternion-algebra-bp.md)
- [The supersingular isogeny path and endomorphism ring problems](isogeny-path-and-endring-problems.md)

## Proof depends on

- [The Deuring correspondence between supersingular curves and maximal orders](deuring-correspondence.md)

## Sources

- David Kohel, Kristin Lauter, Christophe Petit, Jean-Pierre Tignol, "On the Quaternion l-Isogeny Path Problem", LMS Journal of Computation and Mathematics 17A (2014), arXiv:1406.0981.
- Kirsten Eisenträger, Sean Hallgren, Kristin Lauter, Travis Morrison, Christophe Petit, "Supersingular Isogeny Graphs and Endomorphism Rings: Reductions and Solutions", EUROCRYPT (2018), IACR ePrint 2018/371, Theorem 10.
