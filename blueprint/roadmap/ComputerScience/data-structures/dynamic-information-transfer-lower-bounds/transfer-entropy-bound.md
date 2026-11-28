# Information transfer must carry the entropy of the interleaved updates

On the bit-reversal sequence over a group $G$ with at least $2^{\delta}$ elements, served by a structure with $w$-bit cells, $w \ge \lg m$, that answers every query correctly (deterministic or Las Vegas, as in Pătraşcu–Demaine, Section 5), the information-transfer tree is the complete binary tree whose leaves are the $2n$ operations in time order, so that each node splits its aligned dyadic block of operations at the midpoint into a left interval $L_v$ and a right interval $R_v$. For such a node $L_v$ contains $k$ updates and $R_v$ contains $k$ queries, and, listing the updated indices $a_1 < \dots < a_k$ and the queried indices $b_1 < \dots < b_k$, they alternate as $a_1 \le b_1 < a_2 \le b_2 < \dots < a_k \le b_k$, with equality only at the lowest level, where $L_v$ and $R_v$ are a single $\mathrm{update}(i)$ and the matching $\mathrm{sum}(i)$ (the bit-reversal recursion, Pătraşcu–Demaine, Section 5.6). The alignment is a hypothesis: a balanced split elsewhere can pair update intervals with query intervals whose indices do not interleave, and then a query may reveal nothing about $L_v$ even when $k = 1$. Every node $v$ of the aligned tree satisfies

$$
2w \cdot \mathbb{E}\big[|\mathrm{IT}(v)|\big] \ge H(S \mid Z) = \Omega(k\delta),
$$

where $S$ is the vector of sums queried in $R_v$ and $Z$ fixes every operation outside $L_v$; hence $\mathbb{E}[|\mathrm{IT}(v)|] = \Omega(k\delta/w)$ (Pătraşcu–Demaine, Lemmas 5.1 and 5.3).

## Proof sketch

By the alternation, the sum queried at $b_t$ contains the term written at $a_t$ in $L_v$ but none written at $a_{t+1}, \dots, a_k$, so each of the $k$ queried sums contains a fresh uniformly random term from $L_v$, so the sums are independent and uniform given $Z$ and $H(S \mid Z) \ge k\delta$. Encode $S$ given $Z$ by the addresses and contents of the cells in $\mathrm{IT}(v)$, $2w$ bits per cell. The decoder runs the structure up to the start of $L_v$, skips $L_v$, and runs it on $R_v$: a cell read there was written during $R_v$ (the decoder tracks those writes), or is listed in the encoding (it recognizes the address), or was last written before $L_v$ (its content is in the decoder's saved state). Because every answer is correct, the run returns $S$, so the expected encoding length is at least $H(S \mid Z)$; a structure whose answers may err would need the encoding to also correct those errors.

## Depends on

- [Bit-reversal interleaved operation sequence](bit-reversal-hard-sequence.md)
- [Information transfer and the information-transfer tree](information-transfer-tree.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041, Sections 5.3–5.6.
