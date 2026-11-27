# Information transfer must carry the entropy of the interleaved updates

On the bit-reversal sequence over a group $G$ with at least $2^{\delta}$ elements, served by a structure with $w$-bit cells, $w \ge \lg m$, every node $v$ of the information-transfer tree whose left interval contains $k$ updates and whose right interval contains $k$ queries satisfies

$$
2w \cdot \mathbb{E}\big[|\mathrm{IT}(v)|\big] \ge H(S \mid Z) = \Omega(k\delta),
$$

where $S$ is the vector of sums queried in $R_v$ and $Z$ fixes every operation outside $L_v$; hence $\mathbb{E}[|\mathrm{IT}(v)|] = \Omega(k\delta/w)$ (Pătraşcu–Demaine, Lemmas 5.1 and 5.3).

## Proof sketch

By the interleaving, each of the $k$ queried sums contains a fresh uniformly random term from $L_v$, so the sums are independent and uniform given $Z$ and $H(S \mid Z) \ge k\delta$. Encode $S$ given $Z$ by the addresses and contents of the cells in $\mathrm{IT}(v)$, $2w$ bits per cell. The decoder runs the structure up to the start of $L_v$, skips $L_v$, and runs it on $R_v$: a cell read there was written during $R_v$ (the decoder tracks those writes), or is listed in the encoding (it recognizes the address), or was last written before $L_v$ (its content is in the decoder's saved state). The run returns $S$, so the expected encoding length is at least $H(S \mid Z)$.

## Depends on

- [Bit-reversal interleaved operation sequence](bit-reversal-hard-sequence.md)
- [Information transfer and the information-transfer tree](information-transfer-tree.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
