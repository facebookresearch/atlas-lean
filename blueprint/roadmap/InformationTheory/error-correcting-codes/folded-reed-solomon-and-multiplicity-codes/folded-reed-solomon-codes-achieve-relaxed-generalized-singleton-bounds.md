# Chen-Zhang: explicit FRS and multiplicity codes achieve relaxed generalized Singleton bounds

Let $L \in [s]$. (1) A folded Reed-Solomon code of length $n$ and rate $R$ over $\mathbb{F}_q^s$, with $\gamma$ a generator of $\mathbb{F}_q^{\times}$ and evaluation points $\alpha_1, \dots, \alpha_n$ for which the $sn$ points $\gamma^{j}\alpha_i$ are distinct, is

$$
\left( \frac{L}{L+1}\Big(1 - \frac{sR}{s-L+1}\Big),\ L \right)\text{-list decodable.}
$$

(2) A univariate multiplicity code of length $n$ and rate $R$ over $\mathbb{F}_p^s$ with distinct evaluation points is list decodable with the same parameters.

## Proof sketch

Suppose $L + 1$ distinct messages are close to a received word and consider their agreement sets. Within the Guruswami-Wang subspace one tracks, for each coordinate, the dimension of the space of candidates agreeing there; a potential function argument combining folded Wronskian (respectively Wronskian) non-vanishing with the degree bound $k - 1$ for the number of zeros with multiplicity shows that the total agreement cannot exceed what the relaxed generalized Singleton bound allows. The argument is a sharp, explicit analogue of the generic-matrix dimension count behind higher order MDS codes.

## Depends on

- [Folded Reed-Solomon codes](folded-reed-solomon-codes.md)
- [Univariate multiplicity codes](univariate-multiplicity-codes.md)
- [List recovery and relaxed generalized Singleton bounds](list-recovery-of-folded-codes.md)

## Proof depends on

- [Folded Wronskian criterion for linear independence](folded-wronskian-criterion-for-linear-independence.md)
- [Guruswami-Wang: the list of folded RS and multiplicity codes lies in a low-dimensional subspace](linear-algebraic-list-decoding-into-a-subspace.md)

## Sources

- Yeyuan Chen, Zihan Zhang, "Explicit folded Reed-Solomon and multiplicity codes achieve relaxed generalized Singleton bounds", STOC (2025); arXiv:2408.15925 (Definition 1.2, Theorems 1.3 and 1.5).
