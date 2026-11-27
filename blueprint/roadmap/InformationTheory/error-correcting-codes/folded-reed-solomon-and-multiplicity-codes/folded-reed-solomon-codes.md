# Folded Reed-Solomon codes

Let $\gamma \in \mathbb{F}_q^{*}$ have multiplicative order at least $k$, let $s \ge 1$, and let $\alpha_1, \dots, \alpha_n \in \mathbb{F}_q^{*}$ be such that the $sn$ points $\gamma^{j}\alpha_i$ ($0 \le j < s$) are distinct. The *folded Reed-Solomon code* $\mathrm{FRS}^{(s)}_k$ over the alphabet $\mathbb{F}_q^s$ maps $f \in \mathbb{F}_q[x]$ with $\deg f < k$ to

$$
\Big( \big(f(\alpha_i), f(\gamma\alpha_i), \dots, f(\gamma^{s-1}\alpha_i)\big) \Big)_{i=1}^{n} \in (\mathbb{F}_q^{s})^{n},
$$

of rate $R = k/(sn)$. The classical choice is $\alpha_i = \gamma^{s(i-1)}$ with $\gamma$ a primitive element and $sn \le q - 1$.

## Depends on

- [Reed-Solomon code](../reed-solomon-codes/code.md)

## Sources

- Venkatesan Guruswami, Atri Rudra, "Explicit codes achieving list decoding capacity: error-correction with optimal redundancy", IEEE Transactions on Information Theory 54(1) (2008), STOC (2006).
- Yeyuan Chen, Zihan Zhang, "Explicit folded Reed-Solomon and multiplicity codes achieve relaxed generalized Singleton bounds", STOC (2025); arXiv:2408.15925.
