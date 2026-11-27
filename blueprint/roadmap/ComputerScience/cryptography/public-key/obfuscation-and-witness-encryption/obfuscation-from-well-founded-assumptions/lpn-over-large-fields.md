# Learning parity with noise over large prime fields with sparse errors

Let $p$ be a $\lambda$-bit prime, $\ell$ the dimension, $n=\mathrm{poly}(\ell)$ the number of samples and $\delta\in(0,1)$. The *LPN assumption over $\mathbb{Z}_p$ with error rate $\ell^{-\delta}$* states that

$$
(\mathbf{A},\;\mathbf{s}\mathbf{A}+\mathbf{e})\approx_c(\mathbf{A},\;\mathbf{u}),
$$

where $\mathbf{A}\leftarrow\mathbb{Z}_p^{\ell\times n}$, $\mathbf{s}\leftarrow\mathbb{Z}_p^{1\times\ell}$, $\mathbf{u}\leftarrow\mathbb{Z}_p^{1\times n}$ are uniform, and each coordinate of $\mathbf{e}$ is independently $0$ with probability $1-\ell^{-\delta}$ and uniform in $\mathbb{Z}_p$ otherwise. Unlike LWE, the noise is sparse but of arbitrary magnitude.

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317.
