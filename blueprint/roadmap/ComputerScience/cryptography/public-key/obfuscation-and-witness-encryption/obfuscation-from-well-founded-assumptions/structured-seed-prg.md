# Structured-seed pseudorandom generators

A *structured-seed PRG (sPRG)* over $\mathbb{Z}_p$ consists of a seed sampler producing a public seed $\mathsf{P}$ and a private seed $\mathsf{S}\in\mathbb{Z}_p^{n'}$, and an evaluation $\mathsf{Eval}(\mathsf{P},\mathsf{S})\in\{0,1\}^{m}$ such that: (i) every output coordinate is a polynomial of degree at most $2$ in $\mathsf{S}$ whose coefficients are efficiently computable from $\mathsf{P}$ (constant degree in $\mathsf{P}$); (ii) the stretch is polynomial, $m\ge(n')^{1+\tau}$ for a constant $\tau>0$, counting the private seed length; and (iii) $(\mathsf{P},\mathsf{Eval}(\mathsf{P},\mathsf{S}))\approx_c(\mathsf{P},U_m)$.

## Depends on

- [Pseudorandom generators in NC0 with polynomial stretch](local-prg.md)

## Sources

- Aayush Jain, Huijia Lin, Amit Sahai, "Indistinguishability Obfuscation from Well-Founded Assumptions", STOC (2021), IACR ePrint 2020/1003, arXiv:2008.09317.
