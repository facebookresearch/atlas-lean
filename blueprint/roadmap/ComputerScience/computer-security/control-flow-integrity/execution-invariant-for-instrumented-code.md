# Execution invariant for instrumented code

**Lemma.** Let $S_0 = (M_c \mid M_d, R, pc)$ with $pc = 0$ and $I(M_c, G)$ for a [control-flow graph](control-flow-graphs-of-machine-code.md) $G$ of $M_c$
([well-instrumented code](cfi-instrumentation-conditions.md)), and let $S_0 \to \cdots \to S_n$ in the [machine under attack](machine-code-under-attack.md). Then (1) $S_n.M_c = S_0.M_c$; (2)
$S_n.pc \in \mathrm{dom}(S_0.M_c)$; and if $n > 0$, (3) either $S_{n-1} \to_a S_n$ with $S_n.pc = S_{n-1}.pc$, or $S_n.pc \in \mathrm{succ}(S_0.M_c, G, S_{n-1}.pc)$; and (4) if one of the instructions at
$S_n.pc, \dots, S_n.pc + 4$ is a $\mathtt{jmp}$, then $S_{n-1}.pc \in \{S_n.pc, S_n.pc - 1\}$: no step jumps into or past the checks before a computed jump.

The proof is by complete induction on $n$, by cases on the last step and, for a normal step, on its instruction.

## Depends on

- [Well-instrumented code for control-flow integrity](cfi-instrumentation-conditions.md)
- [Machine code under a memory-corrupting attacker](machine-code-under-attack.md)
- [Control-flow graphs of machine code](control-flow-graphs-of-machine-code.md)

## Proof depends on

- [Checked computed jumps reach the expected label](checked-jump-sequences-reach-their-label.md)

## Sources

- M. Abadi, M. Budiu, Ú. Erlingsson and J. Ligatti, "Control-flow integrity: principles, implementations, and applications", *ACM Transactions on Information and System Security* 13(1), 2009; numbering of the author version of February 2007, <https://cseweb.ucsd.edu/~dstefan/cse127-winter19/papers/abadi:cfi.pdf>: Appendix A.1, Lemma 4 and its proof.
