# Logarithmic-derivative lookups as a degree-two special-sound protocol

For a lookup of $\mathbf{w}\in\mathbb{F}^{n}$ into a table $\mathbf{t}\in\mathbb{F}^{T}$ with distinct entries, over a field with $\operatorname{char}\mathbb{F}>\max(n,T)$, the following 3-move protocol is $(n+T)$-special sound with an algebraic verifier of degree $2$: the prover sends multiplicities $\mathbf{m}\in\mathbb{F}^{T}$; the verifier sends $r$; the prover sends $h_i=1/(w_i+r)$ and $g_j=m_j/(t_j+r)$; the verifier checks $h_i(w_i+r)=1$ for all $i$, $g_j(t_j+r)=m_j$ for all $j$, and $\sum_ih_i=\sum_jg_j$. The prover's work is linear in $n$ plus the number of nonzero multiplicities, independent of $T$ for entries with $m_j=0$, which is what makes lookups cheap inside ProtoStar's accumulation.

## Proof sketch

All checks are polynomial equations of degree at most $2$ in the transcript. If $\mathbf{w}$ contains an element outside the table, the rational identity $\sum_i 1/(X+w_i)=\sum_j m_j/(X+t_j)$ fails, so it fails at all but at most $n+T-1$ values of $r$; with $n+T$ distinct accepting challenges the identity holds as rational functions. By the logarithmic-derivative lemma, over a field of characteristic greater than $\max(n,T)$ the set $\{w_i\}$ is contained in $\{t_j\}$ iff there are field elements $m_j$ with $\sum_i 1/(X+w_i)=\sum_j m_j/(X+t_j)$, which yields membership.

## Depends on

- [Special-sound protocols with algebraic degree-d verifiers](special-sound-algebraic-verifier.md)

## Sources

- Benedikt Bünz, Binyi Chen, "Protostar: Generic Efficient Accumulation/Folding for Special-Sound Protocols", ASIACRYPT (2023), IACR ePrint 2023/620, Section 4.3 (Lemma 4, restating the logarithmic-derivative lemma, and the protocol $\Pi_{\mathrm{LK}}$).
