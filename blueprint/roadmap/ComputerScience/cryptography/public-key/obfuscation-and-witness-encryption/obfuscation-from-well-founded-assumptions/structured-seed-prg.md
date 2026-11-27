# Structured-seed pseudorandom generators

A *structured-seed PRG (sPRG)* over $\mathbb{Z}_p$ with stretch $\tau$ consists of probabilistic polynomial-time algorithms $\mathsf{IdSamp}(1^\lambda,1^n)\to I$, $\mathsf{SdSamp}(I)\to\mathsf{sd}=(\mathsf{P},\mathsf{S})$, a binary public seed $\mathsf{P}$ and a binary private seed $\mathsf{S}$ of combined length $n\cdot\mathrm{poly}(\lambda)$ for a fixed polynomial, and $\mathsf{Eval}(I,\mathsf{sd})\in\{0,1\}^{m}$ with $m=n^{\tau}$; it has *polynomial stretch* if $\tau>1$. Stretch is thus measured against $n$, while the whole seed has length $n\cdot\mathrm{poly}(\lambda)$; it still expands because $n$ may be any polynomial in $\lambda$. The sPRG is in $(\mathsf{arith}\text{-}\mathsf{NC}^0,\deg 2)$ if $\mathsf{Eval}(I,\mathsf{sd})=Q_I(\mathsf{Process}_I(\mathsf{P}),\mathsf{S})$ over $\mathbb{Z}_p$, where $\mathsf{Process}_I$ is computed in $\mathsf{arith}\text{-}\mathsf{NC}^0$ and $Q_I$ has degree $1$ in its first argument and degree $2$ in $\mathsf{S}$. For a time bound $T$ and $\gamma\in(0,1)$, it is *$(T,\gamma)$-pseudorandom* if every adversary running in time $T$ distinguishes $(I,\mathsf{P},\mathsf{Eval}(I,\mathsf{sd}))$ from $(I,\mathsf{P},U_m)$ with advantage at most $\gamma$; *$\gamma$-pseudorandom* means $(T,\gamma)$-pseudorandom for every polynomial $T$. The parameter $\gamma$ need not be negligible.

## Depends on

- [Pseudorandom generators in NC0 with polynomial stretch](local-prg.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317, Definitions 3.1, 3.2 and 3.3.
