# Observation consistency is undecidable for one-turn deterministic pushdown automata

Observation consistency and its modified form are conditions under which hierarchical supervisory control under partial observation preserves normality. Both are undecidable for plants given by one-turn deterministic pushdown automata, a model only slightly more expressive than finite automata.

**Setting (Komenda and Masopust).** Let $\Sigma$ be a finite alphabet with subsets $\Sigma_{hi}$ of *high-level events* and $\Sigma_o$ of *observable events*. The *projection* $R : \Sigma^* \to \Gamma^*$ onto a subalphabet $\Gamma$ deletes the letters outside $\Gamma$; write $Q$ for the projection onto $\Sigma_{hi}$, $P$ for the projection onto $\Sigma_o$, and $P_{hi}$ for the projection of $\Sigma_{hi}^*$ onto $\Sigma_{hi} \cap \Sigma_o$. A prefix-closed language $L \subseteq \Sigma^*$ is *observation consistent* (OC) if for all $t, t' \in Q(L)$ with $P_{hi}(t) = P_{hi}(t')$ there are $s, s' \in L$ with $Q(s) = t$, $Q(s') = t'$ and $P(s) = P(s')$. It is *modified observation consistent* (MOC) if for every $s \in L$ and every $t' \in Q(L)$ with $P_{hi}(Q(s)) = P_{hi}(t')$ there is $s' \in L$ with $Q(s') = t'$ and $P(s') = P(s)$; MOC implies OC. A *one-turn deterministic pushdown automaton* is a deterministic pushdown automaton whose stack, along every computation, first only grows and then only shrinks.

**Theorem (Komenda and Masopust).** It is undecidable, given a one-turn deterministic pushdown automaton accepting a prefix-closed language $L$ and subalphabets $\Sigma_{hi}, \Sigma_o \subseteq \Sigma$, whether $L$ is observation consistent; the same holds for modified observation consistency.

For plants given by finite automata, the same paper proves both problems PSPACE-hard and leaves their decidability open.

## Depends on

- [Deterministic pushdown automaton](../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/deterministic-context-free-languages/is-deterministic.md)
- [Language accepted by a pushdown automaton](../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/pushdown-automata/accepts.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces the Post correspondence problem. For lists $(w_1, \dots, w_n)$ and $(u_1, \dots, u_n)$ with $w_i \ne u_i$, let $E = \{1, \dots, n\}$ and

$$
L = \{ i_1 \cdots i_m \,\diamond\, w_{i_m}^R \cdots w_{i_1}^R \,@ : m \ge 1 \} \cup \{ i_1 \cdots i_m \,\diamond'\, u_{i_m}^R \cdots u_{i_1}^R \,\# : m \ge 1 \},
$$

where $x^R$ is the reversal of $x$ and $\diamond, \diamond', @, \#$ are new letters. A one-turn deterministic pushdown automaton pushes the indices and then pops them while reading the reversed words, and accepts the prefix closure $\overline{L}$. With $\Sigma_{hi} = \Sigma \cup E \cup \{@, \#\}$ and $\Sigma_o = \Sigma \cup E \cup \{\diamond, \diamond'\}$, a solution $i_1, \dots, i_k$ gives two high-level strings with equal high-level observations whose low-level preimages are told apart by $\diamond$ and $\diamond'$, so $\overline{L}$ is not OC and hence not MOC; if the instance has no solution, $\overline{L}$ is MOC and hence OC.

## Sources

- Jan Komenda and Tomáš Masopust, *Hierarchical Supervisory Control Under Partial Observation: Normality*, IEEE Transactions on Automatic Control 68 (2023), no. 12, 7286–7298, https://doi.org/10.1109/TAC.2023.3257232; the definitions of OC and MOC and the undecidability theorem for one-turn deterministic pushdown automata in the appendix, read in arXiv:2203.01444v3. Locators in arXiv:2203.01444v3: Theorems 15 and 19.
