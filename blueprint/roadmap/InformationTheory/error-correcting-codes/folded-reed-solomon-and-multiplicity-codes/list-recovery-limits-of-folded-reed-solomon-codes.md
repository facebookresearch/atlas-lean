# Limits on list recovery of folded Reed-Solomon codes

For integers $\ell \ge 2$ and $L \ge \ell$, let $m = \lceil \log_\ell(L+1) \rceil$. Folded Reed-Solomon codes of rate $R$ are not

$$
\left( \frac{L + 1 - \ell}{L + 1}\Big(1 - \frac{mR}{m - 1}\Big) + o(1),\ \ell,\ L \right)\text{-list recoverable},
$$

and they are $\big(\frac12 - \frac{sR}{s-2}, 2, 3\big)$-list recoverable, showing the bound is tight in the smallest nontrivial case $\ell = 2$, $L = 3$.

## Proof sketch

For the impossibility, construct input lists by taking $m$ low-degree polynomials and using at each coordinate the $\ell$-ary expansions of their combinations: the $\ell^m \ge L + 1$ codewords $\sum_j c_j f_j$ with digits $c_j \in [\ell]$ all lie in the lists on most coordinates, the degrees of freedom being counted by a polynomial-method dimension argument. Tightness for $(2, 3)$ follows from the same potential argument as for list decoding.

## Depends on

- [List recovery and relaxed generalized Singleton bounds](list-recovery-of-folded-codes.md)
- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)

## Proof depends on

- [Chen-Zhang: explicit FRS and multiplicity codes achieve relaxed generalized Singleton bounds](folded-reed-solomon-codes-achieve-relaxed-generalized-singleton-bounds.md)

## Sources

- Yeyuan Chen, Zihan Zhang, "Explicit folded Reed-Solomon and multiplicity codes achieve relaxed generalized Singleton bounds", STOC (2025); arXiv:2408.15925.
