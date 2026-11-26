# Pseudorandom generators in NC0 with polynomial stretch

A function family $G:\{0,1\}^{n}\to\{0,1\}^{m}$ with $m=n^{1+\tau}$ for a constant $\tau>0$ is a *PRG in $\mathsf{NC}^{0}$ with polynomial stretch* if each output bit depends on at most a constant number $k$ of input bits, $G$ is computable in polynomial time, and $G(U_n)$ is computationally indistinguishable from $U_m$. A standard candidate is *Goldreich's construction*: fix a $k$-uniform hypergraph $H$ with $m$ hyperedges $S_1,\dots,S_m\subseteq[n]$ (chosen at random) and a predicate $P:\{0,1\}^{k}\to\{0,1\}$, and set $G_{H,P}(x)_i=P(x|_{S_i})$; polynomial stretch requires $P$ to have sufficiently high algebraic degree and resiliency (e.g., XOR-AND type predicates).

## Depends on

- [Pseudorandom generators exist if and only if one-way functions exist](../../../symmetric-key/pseudorandom-generators/pseudorandom-generators-exist-if-and-only-if.md)

## Sources

- Oded Goldreich, "Candidate One-Way Functions Based on Expander Graphs", ECCC TR00-090 (2000); in Studies in Complexity and Cryptography (2011).
- Benny Applebaum, Yuval Ishai, Eyal Kushilevitz, "Cryptography in NC^0", SIAM Journal on Computing (2006).
- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317.
