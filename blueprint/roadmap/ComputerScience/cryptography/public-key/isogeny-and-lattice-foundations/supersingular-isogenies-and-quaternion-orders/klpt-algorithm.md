# KLPT: ideals of powersmooth or prime-power norm in a special maximal order

Let $p\equiv 3\pmod 4$ and $\mathcal{O}_0=\mathbb{Z}\langle i,\frac{1+j}{2}\rangle$-type special maximal order of $B_{p,\infty}$ (containing $\mathbb{Z}[i]$ with $i^{2}=-1$). There is a probabilistic algorithm that, given a left $\mathcal{O}_0$-ideal $I$ and a prime $\ell$, outputs an equivalent left ideal $J=I\gamma$ of norm $\ell^{e}$ with $\ell^{e}\approx p^{7/2}$ (or of powersmooth norm), running in time polynomial in $\log p$ and $\log\ell$ under heuristic assumptions on the distribution of represented primes. Via the Deuring correspondence this solves the $\ell$-isogeny path problem in polynomial time between curves whose endomorphism rings are known.

## Proof sketch

First find an equivalent ideal of prime norm. Then solve norm equations of the form $\mathrm{nrd}(\gamma)=N(I)\ell^{e}$ in $\mathcal{O}_0$ using the special structure: solve $x^{2}+y^{2}+p(z^{2}+w^{2})=M$ by choosing $z,w$ to satisfy congruence conditions modulo $N(I)$ (strong approximation) and then representing the remainder as a sum of two squares via Cornacchia, which succeeds heuristically for many trials. The size $p^{7/2}$ arises from the lattice reductions and congruence conditions.

## Depends on

- [The quaternion algebra ramified at p and infinity and its maximal orders](quaternion-algebra-bp.md)
- [The supersingular isogeny path and endomorphism ring problems](isogeny-path-and-endring-problems.md)

## Proof depends on

- [The Deuring correspondence between supersingular curves and maximal orders](deuring-correspondence.md)

## Sources

- David Kohel, Kristin Lauter, Christophe Petit, Jean-Pierre Tignol, "On the Quaternion l-Isogeny Path Problem", LMS Journal of Computation and Mathematics 17A (2014), arXiv:1406.0981.
