# Programmable bootstrapping in TFHE

Let $f:\mathbb{Z}_{2N}\to\mathbb{T}$ be negacyclic. Given a TLWE sample $c$ under $\mathbf{s}\in\{0,1\}^{n}$ with phase $\varphi$, bootstrapping keys $\mathrm{BK}_i$ (TRGSW encryptions of $s_i$ under a TRLWE key $\mathbf{s}''$) and key-switching keys from $\mathbf{s}''$ (extracted) to $\mathbf{s}$, the procedure blind rotation with test polynomial for $f$, sample extraction and key switching outputs a TLWE sample under $\mathbf{s}$ of $f(\bar{\varphi})$, where $\bar{\varphi}=\lfloor 2N\varphi\rceil$ up to an additional rounding error of the $\bar{a}_i$ of variance at most $(n+1)/(48N^{2})$ in units of the torus. Its output error variance is bounded by $n\bigl((k+1)\ell N\beta^{2}\vartheta_{\mathrm{BK}}+(1+kN)\epsilon^{2}\bigr)+kNt\,\vartheta_{\mathrm{KS}}+kN2^{-2(t\gamma+1)}$, independent of the input error. In particular, if the input phase is within the rounding tolerance of a message in a discrete set, any negacyclic lookup table of the message is computed with refreshed noise.

## Proof sketch

Compose the blind-rotation, sample-extraction and key-switching lemmas; the noise bounds add. The rounding of $\mathbf{a}$ and $b$ to $\mathbb{Z}_{2N}$ introduces a phase error that is a sum of $n+1$ independent uniform roundings, each of variance $1/(12\cdot 4N^{2})$; correctness requires this plus the input error to stay inside the decision interval of the lookup table.

## Depends on

- [Blind rotation of a test polynomial by an encrypted phase](blind-rotation.md)
- [Noiseless sample extraction from TRLWE to TLWE](sample-extraction.md)
- [TLWE key switching with additive noise](tlwe-key-switching.md)
- [Programmable bootstrapping evaluates only negacyclic functions](negacyclic-restriction.md)

## Proof depends on

- [Blind rotation of a test polynomial by an encrypted phase](blind-rotation.md)
- [Noiseless sample extraction from TRLWE to TLWE](sample-extraction.md)
- [TLWE key switching with additive noise](tlwe-key-switching.md)

## Sources

- Ilaria Chillotti, Nicolas Gama, Mariya Georgieva, Malika Izabachène, "TFHE: Fast Fully Homomorphic Encryption over the Torus", Journal of Cryptology (2020), IACR ePrint 2018/421.
