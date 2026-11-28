# Replicated three-party secret sharing with zero-sharing multiplication

In *replicated 2-out-of-3 sharing* over $\mathbb{Z}_{2^k}$ a secret $x=x_1+x_2+x_3$ is held as pairs, party $i$ holding $(x_i,x_{i+1})$. To multiply, party $i$ computes $z_i=x_iy_i+x_iy_{i+1}+x_{i+1}y_i+\alpha_i$ with a zero sharing $\alpha_1+\alpha_2+\alpha_3=0$ and sends $z_i$ to party $i-1$ over a private channel.

Indices are modulo $3$. A sharing of $x$ consists of $x_1,x_2,x_3$ uniform subject to $x_1+x_2+x_3=x$; any two parties reconstruct $x$, and a single party's pair is uniform and independent of $x$. Addition and multiplication by a public constant are local, and a public constant is added to one share. For a product, $\sum_iz_i=xy$ because each of the nine terms $x_jy_{j'}$ occurs exactly once among $z_1,z_2,z_3$; after resharing every party again holds a pair. With *ideal* correlated randomness, each zero sharing is uniform on $\{(\alpha_1,\alpha_2,\alpha_3):\sum\alpha_i=0\}$ and party $i$ receives $\alpha_i$. In the *PRF* realization, a one-time setup draws three independent uniform keys $k_1,k_2,k_3$ of a PRF $F$ with outputs in $\mathbb{Z}_{2^k}$ and gives party $i$ the keys $k_i,k_{i+1}$; the $j$-th zero sharing is $\alpha_i=F_{k_i}(j)-F_{k_{i+1}}(j)$, each index used once, which sums to zero and is pseudorandom rather than uniform.

## Depends on

- [Asymptotic PRF security relative to a class of distinguishers](../../symmetric-key/pseudorandom-functions/prfsecure.md)

## Proof depends on

None.

## Expansion

A definition of the sharing and of the multiplication procedure; no security statement is made here. Araki et al.'s Theorem 3.4 states perfect security of their protocol, in a related 2-out-of-3 share format, in a hybrid model with ideal multiplication; the PRF realization and the relation to the pair format above are separate steps.

## Sources

- Payman Mohassel, Peter Rindal, "ABY3: A Mixed Protocol Framework for Machine Learning", ACM CCS 2018, DOI 10.1145/3243734.3243760; authors' full paper [IACR ePrint 2018/403](https://eprint.iacr.org/2018/403), §3.2.1 ("Secret Sharing Based"), before Table 2.
- Toshinori Araki, Jun Furukawa, Yehuda Lindell, Ariel Nof, Kazuma Ohara, "High-Throughput Semi-Honest Secure Three-Party Computation with an Honest Majority", ACM CCS 2016, DOI 10.1145/2976749.2978331; authors' full paper [IACR ePrint 2016/768](https://eprint.iacr.org/2016/768), §§2.2–2.3 and §3 (Theorem 3.4, after Definition 3.2).
