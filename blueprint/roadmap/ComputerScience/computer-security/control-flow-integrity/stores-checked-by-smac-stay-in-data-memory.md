# Stores checked by software memory access control stay in data memory

**Proposition.** If six consecutive instructions of the code memory are $\mathtt{addi}\ r_0, r_d, w$; $\mathtt{movi}\ r_1, \max(M_d)$; $\mathtt{movi}\ r_2, \min(M_d)$; $\mathtt{bgt}\ r_0, r_1, \mathit{HALT}$;
$\mathtt{bgt}\ r_2, r_0, \mathit{HALT}$; $\mathtt{st}\ r_0(0), r_s$, and they are executed in order with one normal step each and any number of attack steps in between, in the permissive semantics of
[SMAC instrumentation](smac-instrumentation-conditions.md), then the store address $R(r_0)$ lies in $\mathrm{dom}(M_d)$ and hence not in code memory. For the analogous ten-instruction jump
sequence of condition 4, executed in the same way from $S_0$ to $S_9$, the target $w = S_9.R(r_0)$ lies in $\mathrm{dom}(M_c)$ and holds the expected immediate value; if moreover
$I_s(M_c, G)$ holds and $S_9.\mathit{pc} \in \mathrm{dom}(M_c)$, then $w$ carries the label of the jump's destination in $G$.

## Depends on

- [Instrumentation for control-flow integrity with software memory access control](smac-instrumentation-conditions.md)

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; numbering of the author version of February 2007, <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Appendix A.2, Propositions 5 and 6.
