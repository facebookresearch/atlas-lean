# Nested metric temporal logic

Nested metric temporal logic (NMTL) extends metric temporal logic with timed versions of the abstract and caller modalities of CaRet, which follow the call–return structure of a word over a pushdown alphabet.

**Definition.** A *timed word* over a finite alphabet $\Sigma$ is a finite or infinite word $(a_0, \tau_0)(a_1, \tau_1)\cdots$ over $\Sigma \times \mathbb R_{\ge 0}$ with nondecreasing timestamps, divergent if infinite. A *pushdown alphabet* splits $\Sigma$ into calls, returns and internal symbols; here, for a set $P$ of propositions containing $\mathit{call}$, $\mathit{ret}$ and $\mathit{int}$, the alphabet $\Sigma_P$ consists of the subsets of $P$ that contain exactly one of $\mathit{call}$, $\mathit{ret}$ and $\mathit{int}$, which classifies the letter (Section 3 of the source). In an untimed word $\sigma$, a return position $j$ is the *matching return* of a call position $i < j$ if $\sigma[i+1, j-1]$ is well-matched. The *abstract successor* of $i$ is its matching return if $i$ is a call (undefined if there is none), and otherwise $i + 1$ unless $i + 1$ is a return or beyond the word (then undefined); the *caller* of $i$ is the greatest call $j_c < i$ whose matching return is absent or after $i$. Let $\mathrm{Pos}(g, \sigma, i)$ be all positions, $\mathrm{Pos}(a, \sigma, i)$ the positions of the maximal path of abstract successors through $i$, and $\mathrm{Pos}(c, \sigma, i)$ the positions of the caller path from $i$. NMTL formulas are

$$
\varphi ::= \top \mid p \mid \varphi \vee \varphi \mid \neg\varphi \mid \varphi\ \widehat{\mathsf U}{}^{\mathit{dir}}_I\ \varphi \mid \varphi\ \widehat{\mathsf S}{}^{\mathit{dir}'}_I\ \varphi,
$$

with $p \in P$, intervals $I \subseteq \mathbb R_{\ge 0}$ with endpoints in $\mathbb N \cup \{\infty\}$, $\mathit{dir} \in \{g, a\}$ and $\mathit{dir}' \in \{g, a, c\}$. For a timed word $w = (\sigma, \tau)$ and a position $i$: $(w, i) \models \varphi_1\,\widehat{\mathsf U}{}^{\mathit{dir}}_I\,\varphi_2$ iff there is $j > i$ in $\mathrm{Pos}(\mathit{dir}, \sigma, i)$ with $(w, j) \models \varphi_2$, $\tau_j - \tau_i \in I$, and $(w, k) \models \varphi_1$ for all $k \in [i+1, j-1] \cap \mathrm{Pos}(\mathit{dir}, \sigma, i)$; the since modalities are symmetric towards the past. *Future NMTL* is the fragment without since modalities; with $\mathit{dir} = g$ only it is future MTL.

## Depends on

- [Metric temporal logic](metric-temporal-logic.md)
- [Timed words and timed languages](../../../TheoryOfComputation/omega-automata-and-games/timed-automata/timed-words-and-timed-languages.md)
- [Visibly pushdown automata and visibly pushdown languages](../../../TheoryOfComputation/context-free-languages/visibly-pushdown-languages/visibly-pushdown-automata.md)

## Proof depends on

None.

## Expansion

The abstract path through a position inside a procedure skips the subcomputations of nested calls, and the caller path follows the stack of pending calls, as in CaRet. The fragment NMITL$_{(0,\infty)}$, which allows only nonsingular intervals with endpoints in $\mathbb N \cup \{\infty\}$ that are unbounded or left-closed with left endpoint $0$, has the same expressive power as the logic EC$_{\mathrm{NTL}}$ of the same paper, and its satisfiability and visibly model checking against visibly pushdown timed automata are EXPTIME-complete (Theorem 5).

## Sources

- L. Bozzelli, A. Murano and A. Peron, "Timed Context-Free Temporal Logics", in *Proceedings of the Ninth International Symposium on Games, Automata, Logics, and Formal Verification (GandALF 2018)*, Electronic Proceedings in Theoretical Computer Science 277, 2018, pp. 235–249, <https://doi.org/10.4204/EPTCS.277.17>; numbers from arXiv:1911.08406v1, <https://arxiv.org/abs/1911.08406v1>: Section 2 (timed words, pushdown alphabets, abstract and caller paths), Section 3 (the pushdown alphabet $\Sigma_P$) and Section 5 (syntax and semantics of NMTL, the fragments, Lemma 1 and Theorem 5).
