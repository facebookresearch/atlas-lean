# Quasispecies distribution in the long-chain limit

**Model.** Genotypes are binary sequences of length $\ell$; each site mutates independently with probability $q$ at replication, so $M(u,v)=q^{d(u,v)}(1-q)^{\ell-d(u,v)}$ with Hamming distance $d$. On the sharp peak landscape a master sequence $w^*$ has fitness $\sigma>1$ and all other genotypes fitness $1$. Stationary concentrations $x(u)\ge0$, $\sum_ux(u)=1$, solve Eigen's system

$$
x(u)\sum_{v}x(v)f(v)=\sum_{v}x(v)f(v)M(v,u).
$$

Lumping by Hamming class $\mathcal H_k$ (distance $k$ from $w^*$), the class concentrations $y(k)=\sum_{u\in\mathcal H_k}x(u)$ satisfy the same type of system with class mutation kernel $M_H(b,c)=\mathbb{P}(b-X+Y=c)$, $X\sim\mathrm{Bin}(b,q)$, $Y\sim\mathrm{Bin}(\ell-b,q)$ independent.

**Long-chain limit.** As $\ell\to\infty$, $q\to0$, $\ell q\to a\in(0,\infty)$, $M_H(b,c)\to e^{-a}a^{c-b}/(c-b)!$ for $c\ge b$ and $0$ otherwise, and the limiting system admits a solution with positive master concentration if and only if $\sigma e^{-a}>1$ (error threshold). Then $y(0)=(\sigma e^{-a}-1)/(\sigma-1)$ and for all $k\ge0$

$$
y(k)=(\sigma e^{-a}-1)\frac{a^k}{k!}\sum_{h\ge1}\frac{h^k}{\sigma^h},
$$

which defines a probability distribution on $\{0,1,2,\dots\}$, the *quasispecies distribution* with parameters $(\sigma,a)$; its generating function is $\sum_ky(k)X^k=(\sigma e^{-a}-1)\,e^{aX}/(\sigma-e^{aX})$. Equivalently, for $k\ge1$,

$$
y(k)=(\sigma e^{-a}-1)\frac{a^k}{k!}\frac{\sigma}{(\sigma-1)^{k+1}}\sum_{h=0}^{k-1}\Bigl\langle {k \atop h}\Bigr\rangle\sigma^h
=(\sigma e^{-a}-1)\frac{a^k}{k!}\frac{\sigma}{\sigma-1}\sum_{h=1}^{k}\frac{h!\,\left\{ {k \atop h} \right\}}{(\sigma-1)^h},
$$

where $\langle{k\atop h}\rangle$ is the number of permutations of $\{1,\dots,k\}$ with exactly $h$ ascents (Eulerian numbers) and $\{{k\atop h}\}$ the number of partitions of a $k$-set into $h$ nonempty blocks (Stirling numbers of the second kind).

## Depends on

- [Eigen's error threshold](../../../eigen-s-quasispecies-error-threshold/master-equilibrium-exp-pos-iff.md)

## Expansion

Since mean fitness equals $(\sigma-1)y(0)+1$ under the normalization, the limiting system is triangular: the $k=0$ equation $y(0)((\sigma-1)y(0)+1)=\sigma e^{-a}y(0)$ fixes $y(0)$, which is positive exactly above the error threshold, and the higher equations give the recursion $\sigma y(k)=\sigma y(0)a^k/k!+\sum_{1\le h\le k}y(h)a^{k-h}/(k-h)!$. Multiplying by $X^k$ and summing turns this into $g(X)e^{aX}=\sigma g(X)-y(0)(\sigma-1)e^{aX}$, and expanding $e^{aX}/(\sigma-e^{aX})$ as a geometric series in $e^{aX}/\sigma$ gives the series formula. The finite forms follow from the classical identities $\sum_{h\ge1}h^ks^h=s(1-s)^{-k-1}\sum_h\langle{k\atop h}\rangle s^h$ with $s=1/\sigma$, the symmetry $\langle{k\atop h}\rangle=\langle{k\atop k-1-h}\rangle$, and $\sum_{h\ge j}\langle{k\atop h}\rangle\binom{h}{j}=(k-j)!\{{k\atop k-j}\}$.

## Sources

- Raphaël Cerf, Joseba Dalmau, *The quasispecies distribution*, arXiv (2016). Sections 2, 4–9 (quasispecies model, Hamming class lumping, long chain regime, the distribution of the quasispecies, Eulerian numbers, Stirling numbers). <https://doi.org/10.48550/arXiv.1609.05738> Published version: R. Cerf and J. Dalmau, The Quasispecies Equation and Classical Population Models, Springer (2022), <https://doi.org/10.1007/978-3-031-08663-2>.
