# The Weil pairing is biadditive, Galois-equivariant and compatible in m

Let $k$, $m$, $A$, $A^\vee$ and $e_m$ be as in [The Weil pairing through a Poincaré divisor](weil-pairing-through-a-poincare-divisor.md).
Then:

1. $e_m$ is biadditive: $e_m(x_1 + x_2, x') = e_m(x_1, x')\,e_m(x_2, x')$ and $e_m(x, x'_1 + x'_2) = e_m(x, x'_1)\,e_m(x, x'_2)$.
2. $e_m$ is Galois-equivariant: $\sigma(e_m(x, x')) = e_m(\sigma x, \sigma x')$ for every automorphism $\sigma$ of $\bar k$ over $k$.
3. For integers $m, n \ge 1$ prime to the characteristic of $k$, $x \in A[mn](\bar k)$ and $x' \in A^\vee[m](\bar k) \subseteq A^\vee[mn](\bar k)$,

    $$e_{mn}(x, x') = e_m(nx, x').$$

Proof. The values $\mathcal{P}(\mathfrak{b}, \mathfrak{b}')$ and ${}^t\mathcal{P}(\mathfrak{b}', \mathfrak{b})$ are multiplicative in each
argument: $\mathcal{P}(\mathfrak{b}_1 + \mathfrak{b}_2)$ is the divisor of $f_1 f_2$, and evaluation of a function on a $0$-cycle is
multiplicative in the cycle. So if $\mathfrak{a}_1$ and $\mathfrak{a}_2$ sum to $x_1$ and $x_2$, then $\mathfrak{a}_1 + \mathfrak{a}_2$
sums to $x_1 + x_2$, and with it the value $e_m(x_1 + x_2, x')$, which does not depend on the cycles chosen, is the
product of the values computed with $\mathfrak{a}_1$ and with $\mathfrak{a}_2$; the same holds in $x'$. For 2, $\mathcal{P}$ is $k$-rational, so $\sigma$ carries the function $f$ with
divisor $\mathcal{P}(\mathfrak{b})$ to one with divisor $\mathcal{P}(\sigma\mathfrak{b})$, and
$\sigma(\mathcal{P}(\mathfrak{b}, \mathfrak{b}')) = \mathcal{P}(\sigma\mathfrak{b}, \sigma\mathfrak{b}')$. For 3, let $\mathfrak{a}$ and
$\mathfrak{a}'$ sum to $x$ and $x'$; then $n\mathfrak{a}$ sums to $nx$, the numerators of both sides are
$\mathcal{P}(mn\mathfrak{a}, \mathfrak{a}')$, and the denominators agree because $m\mathfrak{a}'$ sums to $0$ and
${}^t\mathcal{P}(mn\mathfrak{a}', \mathfrak{a}) = {}^t\mathcal{P}(m\mathfrak{a}', \mathfrak{a})^n = {}^t\mathcal{P}(m\mathfrak{a}', n\mathfrak{a})$.

## Depends on

- [The Weil pairing through a Poincaré divisor](weil-pairing-through-a-poincare-divisor.md)

## Proof depends on

- [The Weil pairing through a Poincaré divisor](weil-pairing-through-a-poincare-divisor.md), for the independence of the value from the cycles chosen

## Sources

- B. Poonen and M. Stoll, *The Cassels-Tate pairing on polarized abelian varieties*, Ann. of Math. (2) 150 (1999),
  1109–1149, doi:10.2307/121064: §12.2, pp. 1143–1144 (the definition of $e_m$, and "Let $\vee$ denote the cup-product
  pairing associated to $e_m$", which treats $e_m$ as a pairing of Galois modules).
