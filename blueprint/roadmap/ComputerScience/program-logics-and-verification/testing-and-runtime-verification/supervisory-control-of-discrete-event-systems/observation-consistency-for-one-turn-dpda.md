# Observation consistency is undecidable for one-turn deterministic pushdown automata

Observation consistency is a condition under which hierarchical supervisory control under partial observation preserves normality. It is undecidable for plants given by one-turn deterministic pushdown automata, a model only slightly more expressive than finite automata.

**Setting (Komenda and Masopust).** Let $\Sigma$ be a finite alphabet with subsets $\Sigma_{hi}$ of *high-level events* and $\Sigma_o$ of *observable events*. The *projection* $R : \Sigma^* \to \Gamma^*$ onto a subalphabet $\Gamma$ deletes the letters outside $\Gamma$; write $Q$ for the projection onto $\Sigma_{hi}$, $P$ for the projection onto $\Sigma_o$, and $P_{hi}$ for the projection of $\Sigma_{hi}^*$ onto $\Sigma_{hi} \cap \Sigma_o$. A prefix-closed language $L \subseteq \Sigma^*$ is *observation consistent* (OC) if for all $t, t' \in Q(L)$ with $P_{hi}(t) = P_{hi}(t')$ there are $s, s' \in L$ with $Q(s) = t$, $Q(s') = t'$ and $P(s) = P(s')$. It is *modified observation consistent* (MOC) if for every $s \in L$ and every $t' \in Q(L)$ with $P_{hi}(Q(s)) = P_{hi}(t')$ there is $s' \in L$ with $Q(s') = t'$ and $P(s') = P(s)$; MOC implies OC. As in the source, a pushdown automaton here is finitely supported (finitely many states, stack symbols and input letters) and comes with a set $F$ of accepting states; it accepts by final state, so $L(M)$ is the set of words $w$ such that the initial configuration of $M$ on $w$ derives a configuration in a state of $F$ with no remaining input and any stack contents. It is *deterministic* in the sense of the linked page. A *one-turn deterministic pushdown automaton* is a deterministic pushdown automaton whose stack, along every computation, first only grows and then only shrinks.

**Theorem (Komenda and Masopust).** It is undecidable, given a one-turn deterministic pushdown automaton accepting a prefix-closed language $L$ and subalphabets $\Sigma_{hi}, \Sigma_o \subseteq \Sigma$, whether $L$ is observation consistent (Theorem 19 of the source).

For plants given by finite automata, the same paper proves verifying OC and MOC PSPACE-hard and leaves their decidability open (Theorem 15). Theorem 19 of the source also claims undecidability of MOC for one-turn deterministic pushdown automata, but its argument for the case without a solution does not cover the prefix-closed language: for the single pair $(w_1, u_1) = (a, aa)$, which has no solution, the low-level string $s = 1 \diamond' a$ and the high-level string $t' = 1 a @$ have $P_{hi}(Q(s)) = 1a = P_{hi}(t')$, while the only $s'$ with $Q(s') = t'$ is $1 \diamond a @$, with $P(s') = 1 \diamond a \ne P(s)$. So the MOC half is not stated here.

## Proof sketch

The proof reduces the Post correspondence problem. For lists $(w_1, \dots, w_n)$ and $(u_1, \dots, u_n)$ of words over an alphabet $\Delta$, with $w_i \ne u_i$, let $E = \{1, \dots, n\}$ and

$$
L = \{ i_1 \cdots i_m \,\diamond\, w_{i_m}^R \cdots w_{i_1}^R \,@ : m \ge 1 \} \cup \{ i_1 \cdots i_m \,\diamond'\, u_{i_m}^R \cdots u_{i_1}^R \,\# : m \ge 1 \},
$$

where $x^R$ is the reversal of $x$ and $\diamond, \diamond', @, \#$ are new letters, so that the plant alphabet is $\Sigma = \Delta \cup E \cup \{\diamond, \diamond', @, \#\}$. A one-turn deterministic pushdown automaton pushes the indices and then pops them while reading the reversed words, and accepts the prefix closure $\overline{L}$. With $\Sigma_{hi} = \Delta \cup E \cup \{@, \#\}$ and $\Sigma_o = \Delta \cup E \cup \{\diamond, \diamond'\}$, a solution $i_1, \dots, i_k$ gives the high-level strings $t = i_1 \cdots i_k w_{i_k}^R \cdots w_{i_1}^R @$ and $t' = i_1 \cdots i_k u_{i_k}^R \cdots u_{i_1}^R \#$ with $P_{hi}(t) = P_{hi}(t')$, whose only preimages in $\overline{L}$ contain $\diamond$ and $\diamond'$ respectively, so $\overline{L}$ is not OC. Conversely, suppose the instance has no solution, and let $t \ne t'$ in $Q(\overline{L})$ have $P_{hi}(t) = P_{hi}(t')$. Then $t$ and $t'$ differ only in a final marker, since $P_{hi}$ deletes only $@$ and $\#$; they cannot be $x@$ and $x\#$, since the index letters and the letters of $\Delta$ are disjoint and $x@, x\# \in Q(\overline{L})$ would give a solution. So, up to symmetry, $t = x$ and $t' = x@$ (or $x\#$). Take for $s'$ the preimage of $t'$ in $\overline{L}$ and for $s$ the string $s'$ without its final marker, a prefix of $s'$; then $Q(s) = t$, $Q(s') = t'$ and $P(s) = P(s')$. So $\overline{L}$ is OC exactly when the instance has no solution. The source argues the second direction through MOC (Lemma 10), which fails as shown above; the direct argument here chooses both preimages, as OC allows.

## Depends on

- [Deterministic pushdown automaton](../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/deterministic-context-free-languages/is-deterministic.md)
- [Pushdown automaton](../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/pushdown-automata/pda.md)
- [Finitely supported pushdown automata](../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/pushdown-automata/finitely-supported.md)
- [Initial configuration of a pushdown automaton](../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/pushdown-automata/init-config.md)
- [Multi-step computation of a pushdown automaton](../../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/pushdown-automata/derives.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Sources

- Jan Komenda and Tomáš Masopust, *Hierarchical Supervisory Control Under Partial Observation: Normality*, IEEE Transactions on Automatic Control 68 (2023), no. 12, 7286–7298, https://doi.org/10.1109/TAC.2023.3257232; the definitions of OC and MOC and the undecidability theorem for one-turn deterministic pushdown automata in the appendix, read in arXiv:2203.01444v3. Locators in arXiv:2203.01444v3: Theorems 15 and 19.
