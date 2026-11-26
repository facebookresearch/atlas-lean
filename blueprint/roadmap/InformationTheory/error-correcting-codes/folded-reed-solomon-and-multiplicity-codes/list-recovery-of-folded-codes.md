# List recovery and relaxed generalized Singleton bounds

A code $C \subseteq \Sigma^n$ is *$(\rho, \ell, L)$-list recoverable* if for all $S_1, \dots, S_n \subseteq \Sigma$ with $|S_i| \le \ell$, at most $L$ codewords $c$ satisfy $|\{i : c_i \notin S_i\}| \le \rho n$; $(\rho, 1, L)$-list recovery is $(\rho, L)$-list decoding. A code of rate $R$ over $\mathbb{F}_q^s$ built from polynomials of degree $< k = Rsn$ attains the *relaxed generalized Singleton bound* for list size $L \in [s]$ if it is

$$
\left( \frac{L}{L+1}\Big(1 - \frac{sR}{s - L + 1}\Big),\ L \right)\text{-list decodable.}
$$

As $s \to \infty$ with $L$ fixed this approaches the generalized Singleton radius $\frac{L}{L+1}(1 - R)$.

## Depends on

- [List-decodable code](../list-decoding/is-list-decodable.md)
- [Generalized Singleton bound for list decoding (Shangguan-Tamo)](../generic-reed-solomon-list-decoding-capacity/generalized-singleton-bound-for-list-decoding.md)

## Sources

- Yeyuan Chen, Zihan Zhang, "Explicit folded Reed-Solomon and multiplicity codes achieve relaxed generalized Singleton bounds", STOC (2025); arXiv:2408.15925.
- Venkatesan Guruswami, Atri Rudra, "Explicit codes achieving list decoding capacity: error-correction with optimal redundancy", IEEE Transactions on Information Theory 54(1) (2008), STOC (2006).
