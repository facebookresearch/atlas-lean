# Guruswami-Rudra: folded Reed-Solomon codes achieve list-decoding capacity

For every $\varepsilon > 0$ and $R \in (0,1)$, folded Reed-Solomon codes with folding parameter $s = \Theta(1/\varepsilon^2)$ have rate $R$ and can be list decoded from a $1 - R - \varepsilon$ fraction of errors in time $n^{O(1/\varepsilon)}$ with output list size $n^{O(1/\varepsilon)}$, over alphabets of size $n^{O(1/\varepsilon^2)}$.

## Proof sketch

Interpolate a nonzero polynomial $Q(x, y_1, \dots, y_m)$ of low weighted degree vanishing with multiplicity at windows of $m + 1$ consecutive unfolded coordinates of the received word. Every close message $f$ satisfies $Q(x, f(x), f(\gamma x), \dots, f(\gamma^{m-1}x)) = 0$. Since $f(\gamma x) \equiv f(x)^q \bmod E(x)$ for the irreducible $E(x) = x^{q-1} - \gamma$, the candidates are roots of a univariate polynomial over the extension field $\mathbb{F}_q[x]/(E)$ of degree at most $q^{m-1}$, giving the list.

## Depends on

- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)

## Proof depends on

- [Guruswami–Sudan list decoding](../list-decoding/exists-interpolant-dvd.md)
- [List-decoding capacity, achievability](../list-decoding/exists-encoding-list-decodable.md)

## Sources

- Venkatesan Guruswami, Atri Rudra, "Explicit codes achieving list decoding capacity: error-correction with optimal redundancy", IEEE Transactions on Information Theory 54(1) (2008), STOC (2006).
