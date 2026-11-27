# Multiplicative functional of degree $n$ (Lyons)

A multiplicative functional of degree $n$ on a set of times $J$ is a map $(s, t) \mapsto X_{s,t}$,
for $s \le t$ in $J$, into the truncated tensor algebra $T^{(n)}$ (tensor series read through
their coefficients on words of length at most $n$) such that $X^0_{s,t} = 1$ and

$$X_{r,t} = X_{r,s} \otimes X_{s,t} \qquad (r \le s \le t),$$

the product computed coefficientwise as in
[the product of tensor series](../signature-of-a-path/tensor-mul.md). It abstracts Chen's
identity: the [signature](../signature-of-a-path/signature.md) of a path with locally integrable velocity is one, in every degree.

## Sources

- T. Lyons, *Differential equations driven by rough signals*, Rev. Mat. Iberoam. 14 (1998),
  Definition 2.1.2.
