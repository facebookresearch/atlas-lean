# Baby-step giant-step evaluation of the diagonal method

For $n\ge1$, $g=\lceil\sqrt n\,\rceil$ and $h=\lceil n/g\rceil$, the diagonal method can be regrouped as $Av=\sum_{k<h}\rho^{gk}\big(\sum_{j<g}\rho^{-gk}(d_{j+gk})\odot\rho^{j}(v)\big)$, so only $g-1$ baby-step and $h-1$ giant-step rotations of the encrypted vector are needed instead of $n-1$.

Let $R$ be a commutative ring and $\rho$ the cyclic rotation of $R^n$, $\rho(v)[s]=v[s+1]$ (indices mod $n$), so that $\rho^i(v)=v\lll i$; $\rho$ is a ring automorphism of $R^n$ with the slotwise product. Let $d_0,\dots,d_{n-1}$ be the generalized diagonals of $A\in R^{n\times n}$ and set $d_i=0$ for $n\le i<gh$. Then

$$
Av=\sum_{i<n}d_i\odot\rho^i(v)=\sum_{k<h}\rho^{gk}\Big(\sum_{j<g}\rho^{-gk}(d_{j+gk})\odot\rho^{j}(v)\Big).
$$

The plaintexts $\rho^{-gk}(d_{j+gk})$ are precomputed. Hence, in a packed scheme whose slots carry a full cyclic rotation by a single automorphism (a "good" dimension in HElib), the product is computed from $\rho^j([v])$ for $1\le j<g$ and $\rho^{gk}$ applied to $h-1$ inner sums: $(g-1)+(h-1)$ ciphertext rotations and at most $gh$ plaintext–ciphertext products, given key-switching keys for those rotations. These are operation counts only. In a "bad" dimension a rotation combines two automorphisms with complementary masks and the source uses a revised algorithm.

## Depends on

- [The diagonal method for a plaintext matrix times an encrypted vector](diagonal-matrix-vector-product.md)

## Proof depends on

None.

## Expansion

Split $i=j+gk$ ($j<g$, $k<h$, covering $[0,gh)\supseteq[0,n)$), factor $\rho^{gk}$ out using $\rho^{j+gk}=\rho^{gk}\rho^j$ and the automorphism property; the padded diagonals contribute zero.

## Sources

- Shai Halevi, Victor Shoup, "Faster Homomorphic Linear Transformations in HElib", CRYPTO 2018, LNCS 10991, DOI 10.1007/978-3-319-96884-1_4; numbers from IACR ePrint 2018/244: Equation (4), §2.3, §4.1 and §6.3 (Algorithm 1).
