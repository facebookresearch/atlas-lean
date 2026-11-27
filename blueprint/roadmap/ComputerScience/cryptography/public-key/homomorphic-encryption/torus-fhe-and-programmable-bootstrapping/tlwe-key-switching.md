# TLWE key switching with additive noise

Let $\mathbf{s}'\in\{0,1\}^{n'}$ and $\mathbf{s}\in\{0,1\}^{n}$, base $2^{\gamma}$ and precision $t$. Key-switching keys $\mathrm{KS}_{i,j,v}$ are TLWE samples under $\mathbf{s}$ of $v\cdot s'_i/2^{\gamma j}$ for $i\le n'$, $1\le j\le t$, $v<2^{\gamma}$, each with error variance $\vartheta_{\mathrm{KS}}$. Given a TLWE sample $(\mathbf{a}',b')$ of $\mu$ under $\mathbf{s}'$, round each $a'_i$ to $t\gamma$ bits, write it in base $2^{\gamma}$ as digits $a'_{i,j}$, and output $(\mathbf{0},b')-\sum_{i,j}\mathrm{KS}_{i,j,a'_{i,j}}$. The result is a TLWE sample of $\mu$ under $\mathbf{s}$ with error variance at most $\vartheta'+n't\,\vartheta_{\mathrm{KS}}+n'2^{-2(t\gamma+1)}$, where $\vartheta'$ is the input error variance.

## Proof sketch

The subtracted combination encrypts $\sum_{i}\tilde{a}'_is'_i$ for the rounded $\tilde{a}'_i$, so the phase becomes $b'-\langle\tilde{\mathbf{a}}',\mathbf{s}'\rangle=\mu+e'+\langle\mathbf{a}'-\tilde{\mathbf{a}}',\mathbf{s}'\rangle$. The rounding error per coordinate is at most $2^{-(t\gamma+1)}$, contributing the last term; $n't$ key samples are summed, contributing the middle term.

## Depends on

- [TLWE and TRLWE samples over the real torus](tlwe-samples.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
