# Structured-seed PRGs from LPN over F_p and local PRGs

Let $d\in\mathbb{N}$, $\delta>0$ and $\tau>1$ be constants and $n=\mathrm{poly}(\lambda)$ non-constant. Assume a constant-locality Boolean PRG with stretch $m=n^{\tau}$ and multilinear degree $d$ over $\mathbb{Z}$, and LPN over $\mathbb{Z}_p$ with dimension $\ell=n^{1/\lceil d/2\rceil}$, $n$ samples and error rate $\ell^{-\delta}$. Then there is a structured-seed PRG with polynomial stretch in $(\mathsf{arith}\text{-}\mathsf{NC}^0,\deg 2)$ that is $\gamma$-pseudorandom for every constant $\gamma>0$, and subexponentially so if both assumptions hold against $2^{\lambda^{\nu}}$-time adversaries for a constant $\nu>0$. It is not shown to be negligibly pseudorandom, because the evaluation outputs zeros when the error positions fall unevenly into the buckets of the construction. In the construction, the public seed contains $\mathbf{A}$ and the LPN samples $\mathbf{b}=\mathbf{s}\mathbf{A}+\mathbf{e}+\mathbf{x}$ masking the local PRG seed $\mathbf{x}\in\{0,1\}^{n}$; the private seed consists of $\mathbf{s}$ and short correction vectors accounting for the sparse error $\mathbf{e}$, so that each local PRG output (a constant-degree function of few bits of $\mathbf{x}=\mathbf{b}-\mathbf{s}\mathbf{A}-\mathbf{e}$) can be rewritten as a degree-$2$ polynomial in the private seed with coefficients depending on the public seed.

## Proof sketch

Outputs whose input bits avoid the sparse error support are degree-$2$ (indeed low-degree) in $\mathbf{s}$ after expanding the constant-locality predicate with the public $\mathbf{b},\mathbf{A}$ and linearization of the products of $\mathbf{s}$-terms. The few outputs touching corrupted coordinates are corrected by a sparse matrix of precomputed values packed into the private seed with sublinear size, using the low error rate. Pseudorandomness follows from LPN (hiding $\mathbf{x}$) and the local PRG.

## Depends on

- [Structured-seed pseudorandom generators](structured-seed-prg.md)
- [Learning parity with noise over large prime fields with sparse errors](lpn-over-large-fields.md)
- [Pseudorandom generators in NC0 with polynomial stretch](local-prg.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317, Theorem 4.1.
