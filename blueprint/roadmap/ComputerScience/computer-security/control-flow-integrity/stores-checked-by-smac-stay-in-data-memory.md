# Stores checked by software memory access control stay in data memory

**Proposition.** If six consecutive instructions of the code memory are $\mathtt{addi}\ r_0, r_d, w$; $\mathtt{movi}\ r_1, \max(M_d)$; $\mathtt{movi}\ r_2, \min(M_d)$; $\mathtt{bgt}\ r_0, r_1, \mathit{HALT}$;
$\mathtt{bgt}\ r_2, r_0, \mathit{HALT}$; $\mathtt{st}\ r_0(0), r_s$, and they are executed in order with one normal step each and any number of attack steps in between, in the permissive semantics of
[SMAC instrumentation](smac-instrumentation-conditions.md), then the store address $R(r_0)$ lies in $\mathrm{dom}(M_d)$ and hence not in code memory. The analogous jump sequence of
condition 4 lands in code memory on the expected label.

## Depends on

- [Instrumentation for control-flow integrity with software memory access control](smac-instrumentation-conditions.md)

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; author version of February 2007 at <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Appendix A.2, Propositions 5 and 6.
