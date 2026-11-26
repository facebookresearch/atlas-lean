# PLONK gate equations with copy constraints

Let $H=\{1,\omega,\dots,\omega^{n-1}\}\subseteq\mathbb{F}^{\times}$ be a multiplicative subgroup of order $n$. A *PLONK constraint system* consists of selector polynomials $q_L,q_R,q_O,q_M,q_C$ of degree $< n$ and a permutation $\sigma$ of the $3n$ wire positions $\{(j,i):j\in\{a,b,c\},\,0\le i< n\}$. Witness polynomials $a,b,c$ of degree $< n$ (and a public-input polynomial $PI$) satisfy it iff for every $x\in H$

$$
q_L(x)a(x)+q_R(x)b(x)+q_O(x)c(x)+q_M(x)a(x)b(x)+q_C(x)+PI(x)=0,
$$

and the wire values are invariant under $\sigma$ (copy constraints): the value at position $p$ equals the value at $\sigma(p)$ for all $p$.

## Sources

- Ariel Gabizon, Zachary J. Williamson, Oana Ciobotaru, "PLONK: Permutations over Lagrange-bases for Oecumenical Noninteractive arguments of Knowledge", IACR ePrint 2019/953 (2019).
