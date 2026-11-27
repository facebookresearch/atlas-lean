# Checked computed jumps reach the expected label

**Proposition.** Let $S_0, \dots, S_5$ be states of the [machine under attack](machine-code-under-attack.md) with code memory $M_c$ whose instructions at $S_0.pc, \dots, S_5.pc$ are
$\mathtt{addi}\ r_0, r_s, 0$; $\mathtt{ld}\ r_1, r_0(0)$; $\mathtt{movi}\ r_2, \mathit{IMM}$; $\mathtt{bgt}\ r_1, r_2, \mathit{HALT}$; $\mathtt{bgt}\ r_2, r_1, \mathit{HALT}$; $\mathtt{jmp}\ r_0$, with
$S_i \to_n \to_a^* S_{i+1}$ for $i < 5$: one normal step from each of $S_0, \dots, S_4$ followed by any number of attack steps, ending in $S_5$, poised to execute the jump. If $w = S_5.R(r_0) \in \mathrm{dom}(M_c)$, then $M_c(w) = \mathit{IMM}$, and if $I(M_c, G)$ ([well-instrumented code](cfi-instrumentation-conditions.md))
then $w$ holds the label instruction that $G$ requires for the jump at $S_5.pc$. Attack steps cannot change the distinguished registers $r_0, r_1, r_2$.

## Depends on

- [Well-instrumented code for control-flow integrity](cfi-instrumentation-conditions.md)
- [Machine code under a memory-corrupting attacker](machine-code-under-attack.md)

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; numbering of the author version of February 2007, <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Appendix A.1, Proposition 3 and the explanation after it.
