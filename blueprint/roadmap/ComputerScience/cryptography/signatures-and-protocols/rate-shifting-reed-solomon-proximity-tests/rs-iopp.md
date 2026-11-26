# Interactive oracle proofs of proximity for Reed–Solomon codes

For a field $\mathbb{F}$, an evaluation domain $L\subseteq\mathbb{F}$ and degree bound $d$, let $\mathrm{RS}[\mathbb{F},L,d]=\{\hat{f}|_L:\hat{f}\in\mathbb{F}[X],\deg\hat{f}< d\}$, of rate $\rho=d/|L|$. A function $f:L\to\mathbb{F}$ is *$\delta$-far* from the code if its relative Hamming distance to every codeword is at least $\delta$. An *interactive oracle proof of proximity (IOPP)* for $\mathrm{RS}[\mathbb{F},L,d]$ with proximity parameter $\delta$ is an IOP in which the verifier has oracle access to $f$ and to the prover's oracle messages, accepts every codeword with probability $1$, and accepts every $\delta$-far $f$ with probability at most the soundness error $\epsilon$. Its *query complexity* is the total number of oracle locations read.

## Depends on

- [Reed-Solomon code](../../../../InformationTheory/error-correcting-codes/reed-solomon-codes/code.md)

## Sources

- Eli Ben-Sasson, Iddo Bentov, Yinon Horesh, Michael Riabzev, "Fast Reed-Solomon Interactive Oracle Proofs of Proximity", ICALP (2018).
- Eli Ben-Sasson, Alessandro Chiesa, Nicholas Spooner, "Interactive Oracle Proofs", TCC (2016).
- Gal Arnon, Alessandro Chiesa, Giacomo Fenzi, Eylon Yogev, "STIR: Reed–Solomon Proximity Testing with Fewer Queries", CRYPTO (2024), IACR ePrint 2024/390.
