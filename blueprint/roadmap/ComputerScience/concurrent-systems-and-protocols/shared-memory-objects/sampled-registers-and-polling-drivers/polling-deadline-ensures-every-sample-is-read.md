# A polling deadline ensures every sample is read before the next

Let the $k$-th publication to the [sampled register](overwrite-register-reads-return-increasing-publications.md) occur at time
$t_k$, with $t_{k+1} - t_k \ge T_{\min} > 0$, and let one driver be the only reader, clocked at frequency $f_{\mathrm{clk}} > 0$.
Suppose that after each publication the driver performs a ready check within $C_{\mathrm{poll}}$ cycles, that a read started after
a check that saw the slot nonempty completes within $C_{\mathrm{read}}$ further cycles, and that interrupts and bus stalls add at
most $C_{\mathrm{irq}} + C_{\mathrm{bus}}$ cycles to this. If

$$\frac{C_{\mathrm{poll}} + C_{\mathrm{read}} + C_{\mathrm{irq}} + C_{\mathrm{bus}}}{f_{\mathrm{clk}}} < T_{\min},$$

then every publication is read before the next one occurs: no publication is overwritten, and the $k$-th successful read
returns publication $k$. So the driver may pair the $k$-th sample it reads with the acquisition time $t_k$.

## Depends on

- [Reads of an overwrite-newest register return increasing publications](overwrite-register-reads-return-increasing-publications.md)

## Sources

- H. Kopetz, *Real-Time Systems: Design Principles for Distributed Embedded Applications*, 2nd edition, Springer, 2011, Chapter 4 (state messages with update-in-place semantics).
- N. A. Lynch, *Distributed Algorithms*, Morgan Kaufmann, 1996, Chapter 8 (automata, traces and simulation relations).
