# The proof ordering of completion is well-founded

Consider a run of [Knuth–Bendix completion](knuth-bendix-completion.md) with reduction ordering $\succ$ and encompassment ordering $\sqsupset$, with unions $E_\infty$ and $R_\infty$. A *proof* of $s \approx t$ in $E_\infty \cup R_\infty$ is a finite sequence $s = s_0, s_1, \dots, s_n = t$ in which each step $(s_{i-1}, s_i)$ is $s_{i-1} \leftrightarrow_{E_\infty} s_i$, $s_{i-1} \to_{R_\infty} s_i$ or $s_{i-1} \leftarrow_{R_\infty} s_i$. Each step gets a cost:

1. $(\{s_{i-1}, s_i\}, -, -)$ for a step with an equation of $E_\infty$, where $-$ denotes an arbitrary term that plays no role in the comparison;
2. $(\{s_{i-1}\}, l, s_i)$ for a step $s_{i-1} \to_{R_\infty} s_i$ with a rule $l \to r$;
3. $(\{s_i\}, l, s_{i-1})$ for a step $s_{i-1} \leftarrow_{R_\infty} s_i$ with a rule $l \to r$.

Costs of steps are compared by the lexicographic combination of the multiset extension of $\succ$ (on the first components, finite multisets of terms), $\sqsupset$ and $\succ$. The cost of a proof is the multiset of the costs of its steps, and the *proof ordering* $\succ_C$ compares proofs by the multiset extension of the ordering on step costs. Here the multiset extension of an ordering $>$ relates finite multisets $M > N$ if $N$ arises from $M$ by replacing a nonempty submultiset by finitely many elements, each smaller than some removed one.

Then $\succ_C$ is a well-founded ordering.

**Proof.** The multiset extension of a well-founded ordering is well-founded, and a lexicographic combination of well-founded orderings is well-founded; $\succ$ and $\sqsupset$ are well-founded.

## Depends on

- [Knuth–Bendix completion](knuth-bendix-completion.md)

## Proof depends on

- [The Dershowitz–Manna multiset ordering is well-founded](../termination/the-multiset-extension-preserves-well-foundedness.md)
- [The encompassment ordering is well-founded](encompassment-ordering-is-well-founded.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 4.6, the costs of proof steps, the proof ordering, and Lemma 4.35, p. 125; Section 1.3, Lemma 1.5, p. 6, for the well-foundedness of lexicographic combinations, and Section 1.4, Theorem 1.10 (c), p. 9, for that of multiset extensions.
