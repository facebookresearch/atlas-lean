# Explicit codes achieving list-decoding capacity with optimal list size O(1/epsilon)

For every $\varepsilon > 0$ and $R \in (0,1)$, folded Reed-Solomon codes and univariate multiplicity codes of rate $R$ with folding parameter $s = \Theta(1/\varepsilon^2)$ are $\big(1 - R - \varepsilon, O(1/\varepsilon)\big)$-list decodable over alphabets of polynomial size $q^s = n^{O(1/\varepsilon^2)}$. This list size is optimal up to constants and exponentially improves the previous bound $(1/\varepsilon)^{O(1/\varepsilon)}$; it resolves the question of Guruswami and Rudra of whether folded Reed-Solomon codes achieve capacity with list size polynomial in $1/\varepsilon$.

## Proof sketch

Apply the Chen-Zhang theorem with $L = \lceil 2/\varepsilon \rceil$ and $s = \lceil 4L/\varepsilon \rceil$: then $\frac{L}{L+1} \ge 1 - \varepsilon/2$ and $\frac{s}{s-L+1} \le 1 + \frac{2L}{s} \le 1 + \varepsilon/2$, so the radius is at least $(1 - \varepsilon/2)(1 - R - \varepsilon/2) \ge 1 - R - \varepsilon$. Optimality of $O(1/\varepsilon)$ follows from the list-decoding capacity converse and the generalized Singleton bound.

## Depends on

- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)
- [Univariate multiplicity codes](univariate-multiplicity-codes.md)
- [List-decodable code](../list-decoding/is-list-decodable.md)

## Proof depends on

- [Chen-Zhang: explicit FRS and multiplicity codes achieve relaxed generalized Singleton bounds](folded-reed-solomon-codes-achieve-relaxed-generalized-singleton-bounds.md)
- [Generalized Singleton bound for list decoding (Shangguan-Tamo)](../generic-reed-solomon-list-decoding-capacity/generalized-singleton-bound-for-list-decoding.md)
- [List-decoding capacity, converse](../list-decoding/exists-many-in-ball.md)

## Sources

- Yeyuan Chen, Zihan Zhang, "Explicit folded Reed-Solomon and multiplicity codes achieve relaxed generalized Singleton bounds", STOC (2025); arXiv:2408.15925.
