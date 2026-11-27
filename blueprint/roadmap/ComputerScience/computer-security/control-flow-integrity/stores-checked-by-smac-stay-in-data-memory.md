# Stores checked by software memory access control stay in data memory

**Proposition.** If six consecutive instructions of the code memory are $\mathtt{addi}\ r_0, r_d, w$; $\mathtt{movi}\ r_1, \max(M_d)$; $\mathtt{movi}\ r_2, \min(M_d)$; $\mathtt{bgt}\ r_0, r_1, \mathit{HALT}$;
$\mathtt{bgt}\ r_2, r_0, \mathit{HALT}$; $\mathtt{st}\ r_0(0), r_s$, held at $S_0.pc, \dots, S_5.pc$ for states with $S_i \to_n \to_a^* S_{i+1}$ for $i < 5$ in the permissive semantics of
[SMAC instrumentation](smac-instrumentation-conditions.md) (one normal step from each of $S_0, \dots, S_4$ and any number of attack steps, ending in $S_5$, poised to execute the store), then the
store address $S_5.R(r_0)$ lies in $\mathrm{dom}(M_d)$ and hence not in code memory. For the ten instructions of condition 4 (the nine checking instructions and $\mathtt{jmp}\ r_0$), held at $S_0.pc, \dots, S_9.pc$ with $S_i \to_n \to_a^* S_{i+1}$ for $i < 9$, so that $S_9$ is poised to execute the jump, the target $w = S_9.R(r_0)$ lies in $\mathrm{dom}(M_c)$ and holds the expected immediate value; if moreover
$I_s(M_c, G)$ holds and $S_9.\mathit{pc} \in \mathrm{dom}(M_c)$, then $w$ carries the label of the jump's destination in $G$.

## Depends on

- [Instrumentation for control-flow integrity with software memory access control](smac-instrumentation-conditions.md)

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; numbering of the author version of February 2007, <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Appendix A.2, Propositions 5 and 6.
