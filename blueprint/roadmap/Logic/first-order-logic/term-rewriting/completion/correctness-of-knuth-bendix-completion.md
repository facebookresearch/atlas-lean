# Correctness of Knuth–Bendix completion

Let $E_0, R_0 \vdash E_1, R_1 \vdash \cdots$ be a fair run of [Knuth–Bendix completion](knuth-bendix-completion.md) with $R_0 = \emptyset$ and $E_* = \emptyset$. A *proof* of $s \approx t$ in $E_\infty \cup R_\infty$ is a finite sequence $s = s_0, s_1, \dots, s_n = t$ in which each step is $s_{i-1} \leftrightarrow_{E_\infty} s_i$, $s_{i-1} \to_{R_\infty} s_i$ or $s_{i-1} \leftarrow_{R_\infty} s_i$; it is a *rewrite proof in $R_*$* if for some $k$ the steps are $s_{i-1} \to_{R_*} s_i$ for $i \le k$ and $s_{i-1} \leftarrow_{R_*} s_i$ for $i > k$. Then

1. every proof in $E_\infty \cup R_\infty$ can be replaced by a rewrite proof in $R_*$ of the same equation;
2. $R_*$ is equivalent to $E_0$: $\approx_{R_*}\ =\ \approx_{E_0}$;
3. $R_*$ is convergent.

**Proof.** Compare proofs by the [proof ordering](the-proof-ordering-of-completion-is-well-founded.md) $\succ_C$, which is well-founded. Every proof that is not a rewrite proof in $R_*$ has an equivalent smaller proof: a step using an equation of $E_\infty$ or a rule of $R_\infty \setminus R_*$ is replaced according to the inference that removed it, and a peak between rules of $R_*$ is replaced by a valley or, for a critical overlap, by a step with the equation that Deduce added, which fairness provides. Well-founded induction gives 1, which together with the preservation of the equational theory gives 2. Since $\to_{R_*}\ \subseteq\ \succ$, $R_*$ terminates, and by 1 it is Church–Rosser, hence confluent.

## Depends on

- [Knuth–Bendix completion](knuth-bendix-completion.md)
- [Confluence of a relation](../confluence-of-a-relation.md)

## Proof depends on

- [Completion steps preserve the equational theory](completion-steps-preserve-the-equational-theory.md)
- [Completion steps preserve orientation](completion-steps-preserve-orientation.md)
- [The proof ordering of completion is well-founded](the-proof-ordering-of-completion-is-well-founded.md)
- [Reduction orderings characterize termination](../reduction-orderings-characterize-termination.md)
- [The Church–Rosser property is equivalent to confluence](../church-rosser-property-and-confluence.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.6, the proof ordering of Bachmair, Dershowitz and Hsiang, Lemmas 4.35 and 4.36 and Theorem 4.37 with its proof, pp. 125–127.
