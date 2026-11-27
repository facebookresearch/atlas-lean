# Programmable bootstrapping in TFHE

Let $f:\mathbb{Z}_{2N}\to\mathbb{T}$ be negacyclic. Let $c=(\mathbf{a},b)$ be a TLWE sample under $\mathbf{s}\in\{0,1\}^{n}$ with phase $\varphi=b-\sum_ia_is_i$, and let $\bar{a}_i=\lfloor 2Na_i\rceil$, $\bar{b}=\lfloor 2Nb\rceil$ and $\bar{\varphi}=\bar{b}-\sum_i\bar{a}_is_i\bmod 2N$, the index used by blind rotation (the difference of the rounded coordinates, not the rounding $\lfloor 2N\varphi\rceil$ of their combination). Given bootstrapping keys $\mathrm{BK}_i$ (TRGSW encryptions of $s_i$ under a TRLWE key $\mathbf{s}''$) and key-switching keys from $\mathbf{s}''$ (extracted) to $\mathbf{s}$, blind rotation with the test polynomial for $f$, sample extraction and key switching output a TLWE sample under $\mathbf{s}$ of $f(\bar{\varphi})$ whose error variance is at most $n\bigl((k+1)\ell N\beta^{2}\vartheta_{\mathrm{BK}}+(1+kN)\epsilon^{2}\bigr)+kNt\,\vartheta_{\mathrm{KS}}+kN2^{-2(t\gamma+1)}$, independent of the input error. Here $\bar{\varphi}/(2N)-\varphi$ is congruent modulo $1$ to $(\bar{b}/(2N)-b)-\sum_i(\bar{a}_i/(2N)-a_i)s_i$, a sum of at most $n+1$ rounding errors of variance $1/(48N^{2})$ each in units of the torus. Consequently, if a message $\mu$ is encoded so that $f$ takes the intended value $f_\mu$ on an interval $I_\mu\subseteq\mathbb{Z}_{2N}$, the output encrypts $f_\mu$ with refreshed noise whenever $\bar{\varphi}\in I_\mu$, which holds when the input error plus this rounding error keeps $\bar\varphi$ inside $I_\mu$. If $\bar{\varphi}$ leaves $I_\mu$, the output encrypts the table entry $f(\bar{\varphi})$ at a wrong index, which may be arbitrarily far from $f_\mu$; this failure is not additive output noise.

## Proof sketch

Blind rotation turns the test polynomial $v$ into an encryption of $X^{-\bar{\varphi}}v$, whose constant coefficient is $f(\bar{\varphi})$ by the choice of $v$; sample extraction is noiseless and key switching adds its own noise, so the output noise bounds add. The phase error from rounding comes from replacing each $a_i$ and $b$ by a multiple of $1/(2N)$, each rounding error being bounded by $1/(4N)$ and, under the usual independence heuristic, uniform with variance $1/(48N^{2})$. Correctness for the intended message is a statement about the index $\bar{\varphi}$ landing in $I_\mu$, not about the size of the output error.

## Depends on

- [Blind rotation of a test polynomial by an encrypted phase](blind-rotation.md)
- [Noiseless sample extraction from TRLWE to TLWE](sample-extraction.md)
- [TLWE key switching with additive noise](tlwe-key-switching.md)
- [Programmable bootstrapping evaluates only negacyclic functions](negacyclic-restriction.md)
- [TLWE and TRLWE samples over the real torus](tlwe-samples.md)
- [TRGSW samples and the gadget decomposition](trgsw-samples.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
