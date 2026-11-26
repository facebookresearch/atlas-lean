# Worst-case hardness of Module-LWE

Let $K=\mathbb{Q}(\xi)$ for a primitive $\nu$-th root of unity $\xi$, with ring of integers $R=\mathbb{Z}[\xi]$ of degree $n=\varphi(\nu)$, let $d$ be the module rank and $N=nd$ the dimension of the module lattices. Let $\varepsilon(N)=N^{-\omega(1)}$, $\alpha\in(0,1)$, and let $q\ge2$ be a modulus of known factorization with $\alpha q>2\sqrt{d}\cdot\omega(\sqrt{\log n})$. There is a quantum reduction from solving $\mathrm{Mod}\text{-}\mathrm{GIVP}^{\eta_\varepsilon}_\gamma$ (generalized independent vectors, relative to the smoothing parameter, on rank-$d$ module lattices over $R$) in the worst case to solving search Module-LWE $\text{M-SLWE}_{q,\Psi_{\le\alpha}}$ with non-negligible advantage, where $\Psi_{\le\alpha}$ is the family of elliptical Gaussian error distributions on $K_{\mathbb{R}}/R^{\vee}$ with all parameters at most $\alpha$, and $\gamma=\sqrt{8Nd}\cdot\omega(\sqrt{\log n})/\alpha$. If moreover $q$ is prime, $q\le\mathrm{poly}(N)$ and $q\equiv1\pmod\nu$, there is a classical polynomial-time reduction from $\text{M-SLWE}_{q,\Psi_{\le\alpha}}$ to decision $\text{M-LWE}_{q,\Upsilon_\alpha}$, where $\Upsilon_\alpha$ samples elliptical Gaussian parameters $r_j=\alpha\sqrt{1+\sqrt{n}\,x_j}$ with independent $x_j\sim\Gamma(2,1)$. A separate modulus-switching reduction from $\text{M-LWE}_{q,\Upsilon_\alpha}$ to $\text{M-LWE}_{p,\Upsilon_\beta}$, for $\beta\ge\alpha\max(1,q/p)\,n^{1/4}N^{1/2}\omega(\log^{2}N)$ and $\alpha q\ge\omega(\sqrt{\log(N)/n})$, extends decision hardness to moduli $p$ of arbitrary arithmetic shape. For $d=1$ the theorem specializes to the Ring-LWE reduction, and for $n=1$ to Regev's LWE reduction.

## Proof sketch

Generalize the Ring-LWE reduction by working with $R$-modules of rank $d$ in place of ideals; discrete Gaussians on module lattices give Module-LWE samples via the dual module, and the iterative quantum step carries over with the module structure.

## Depends on

- [Approximate lattice problems GapSVP and SIVP](gapsvp-and-sivp.md)

## Proof depends on

- [Hardness of Ring-LWE from worst-case problems on ideal lattices](ring-lwe-hardness.md)

## Sources

- Adeline Langlois, Damien Stehlé, "Worst-Case to Average-Case Reductions for Module Lattices", Designs, Codes and Cryptography (2015), Theorems 4.7 and 4.8.
