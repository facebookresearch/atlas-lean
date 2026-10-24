---
article_id: af_daf8d2ff993a91962e4a5495
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: HeckeAlgebra.section6_1_theorem
---

# Theorem (Section 6.1)

Given a Coxeter system $(W, S)$ and structure constants $a_s, b_s$, there is exactly one associative algebra structure on $\mathcal{A}$ (a free $R$-module with $R$-basis $\{T_w : w \in W\}$) so that $T_s T_w = T_{sw}$ if $\ell(sw) > \ell(w)$, $T_s^2 = a_s T_s + b_s T_1$ for all $s \in S$, and with the requirement that $T_1$ is the identity in $\mathcal{A}$. With this associative algebra structure, we also have $T_s T_w = a_s T_w + b_s T_{sw}$ if $\ell(sw) < \ell(w)$. Further, we have the right-handed version of these identities: $T_w T_s = T_{ws}$ if $\ell(ws) > \ell(w)$ and $T_w T_s = a_s T_w + b_s T_{ws}$ if $\ell(ws) < \ell(w)$.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Lemma (Section 6.1)](026-lemma.md)

## Sources

- [Paul Garrett, Buildings and Classical Groups, Section 6.1](../../../../sources/v1/Buildings.md)
