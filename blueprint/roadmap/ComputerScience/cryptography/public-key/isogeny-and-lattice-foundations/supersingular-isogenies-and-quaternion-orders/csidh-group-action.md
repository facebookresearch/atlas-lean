# The CSIDH class group action on F_p-rational supersingular curves

Let $p\equiv 3\pmod 8$ be prime and $\mathcal{E}\ell\ell_p(\mathbb{Z}[\sqrt{-p}])$ the set of $\mathbb{F}_p$-isomorphism classes of supersingular curves over $\mathbb{F}_p$ whose $\mathbb{F}_p$-rational endomorphism ring is $\mathbb{Z}[\sqrt{-p}]$. The ideal class group $\mathrm{Cl}(\mathbb{Z}[\sqrt{-p}])$ acts freely and transitively on this set via $[\mathfrak{a}]\star E=E/E[\mathfrak{a}]$, where $E[\mathfrak{a}]$ is the intersection of the kernels of the endomorphisms in $\mathfrak{a}$. When $p+1=4\ell_1\cdots\ell_n$ for small odd primes $\ell_i$, the action of the classes of $\mathfrak{l}_i=(\ell_i,\pi-1)$ is computable with $\mathbb{F}_p$-rational $\ell_i$-isogenies, giving a non-interactive key exchange $E_{AB}=[\mathfrak{a}][\mathfrak{b}]\star E_0$ with $|\mathrm{Cl}|\approx\sqrt{p}$.

## Proof sketch

This is the theory of complex multiplication restricted to the $\mathbb{F}_p$-rational endomorphism ring (an order in an imaginary quadratic field): ideals act by isogenies with kernels $E[\mathfrak{a}]$, the action factors through the class group, and it is free and transitive on curves with that endomorphism ring. The splitting of $\ell_i$ into $(\ell_i,\pi\pm 1)$ uses that $\pi^{2}=-p$ and $\ell_i\mid p+1$.

## Depends on

- [Supersingular elliptic curves and isogenies](supersingular-curves.md)

## Sources

- Wouter Castryck, Tanja Lange, Chloe Martindale, Lorenz Panny, Joost Renes, "CSIDH: An Efficient Post-Quantum Commutative Group Action", ASIACRYPT (2018), IACR ePrint 2018/383.
