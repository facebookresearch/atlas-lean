# Information transfer must carry the entropy of the interleaved updates

On the bit-reversal sequence over a group $G$ with $\delta$-bit elements, every node $v$ of the information-transfer tree whose left interval contains $k$ updates satisfies $\mathbb{E}\big[|\mathrm{IT}(v)|\big] \cdot (w + \lg m) \ge \Omega(k\delta) - O(\mathbb{E}[t_q |R_v|] \cdot \lg w)$; for deterministic structures, $|\mathrm{IT}(v)| = \Omega\!\left(k \delta / (w + \lg m)\right)$ once $k\delta$ exceeds the cost of encoding which probes of $R_v$ hit $\mathrm{IT}(v)$.

## Proof sketch

Encode the random values $g_t$ written during $L_v$ given everything outside $L_v$: the encoder sends the addresses and contents of the cells in $\mathrm{IT}(v)$ together with, for each probe in $R_v$, whether it hits $\mathrm{IT}(v)$. The decoder simulates the structure on $R_v$, reading cells from the message when flagged and from its own simulation of the state before $L_v$ otherwise, and recovers the answers in $R_v$, which by perfect interleaving determine the $k$ values of $\delta$ bits each. The encoding must therefore have at least $k\delta$ bits of entropy.

## Depends on

- [Bit-reversal interleaved operation sequence](bit-reversal-hard-sequence.md)
- [Information transfer and the information-transfer tree](information-transfer-tree.md)

## Sources

- Mihai Pătraşcu, Erik D. Demaine, "Logarithmic Lower Bounds in the Cell-Probe Model", SIAM Journal on Computing 35(4) (2006), arXiv:cs/0502041.
