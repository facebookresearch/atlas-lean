# Core spanners

A document spanner maps each word to a finite relation of span tuples. Core spanners are built from regex formulas, regular expressions with variable bindings, by union, projection, natural join and selection by string equality, the algebra of Fagin, Kimelfeld, Reiss and Vansummeren.

Fix a finite alphabet $\Sigma$ with $|\Sigma| \ge 2$ and an infinite set $\mathsf{SVars}$ of span variables disjoint from $\Sigma$.

**Spans and spanners.** For $w = a_1 \cdots a_n \in \Sigma^*$, a span of $w$ is an interval $[i, j\rangle$ with $1 \le i \le j \le n + 1$; it describes the subword $w_{[i,j\rangle} = a_i \cdots a_{j-1}$, and spans are equal only if their bounds are. For finite $V \subseteq \mathsf{SVars}$, a $(V, w)$-tuple is a map $\mu \colon V \to \mathrm{Spans}(w)$. A (document) spanner $P$ with variable set $\mathsf{SVars}(P) = V$ maps every $w \in \Sigma^*$ to a set $P(w)$ of $(V, w)$-tuples. $P_1 \subseteq P_2$ means $P_1(w) \subseteq P_2(w)$ for all $w$, and $P_1 = P_2$ means equality for all $w$. The universal spanner $\Upsilon_Y$ over a finite $Y \subseteq \mathsf{SVars}$ maps each $w$ to the set of all $(Y, w)$-tuples.

**Regex formulas.** Regex formulas are regular expressions over $\Sigma$ (with $\emptyset$, $\varepsilon$, concatenation, disjunction and Kleene star) extended by variable bindings $x\{\alpha\}$ for $x \in \mathsf{SVars}$, where no binding occurs under a Kleene star and $\alpha$ binds no $x$ again. Matching a word $w$ is defined by parse trees; a regex formula $\gamma$ is functional if every parse tree of every word contains exactly one binding node for each variable of $\gamma$. A functional regex formula $\gamma$ defines the spanner $[\![\gamma]\!]$ with $[\![\gamma]\!]\,(w) = \{\mu_T \mid T$ a $\gamma$-parse tree for $w\}$, where $\mu_T(x)$ is the span matched by the binding of $x$ in $T$. RGX denotes the functional regex formulas.

**Operators.** For spanners $P, P_1, P_2$: union $P_1 \cup P_2$ (for $\mathsf{SVars}(P_1) = \mathsf{SVars}(P_2)$); projection $\pi_Y P$ restricting all tuples to $Y \subseteq \mathsf{SVars}(P)$; natural join $P_1 \bowtie P_2$, whose $w$-tuples on $\mathsf{SVars}(P_1) \cup \mathsf{SVars}(P_2)$ restrict to tuples of $P_1(w)$ and of $P_2(w)$; and string-equality selection $\zeta^{=}_{x_1, \dots, x_k} P$, keeping the $\mu \in P(w)$ with $w_{\mu(x_1)} = \cdots = w_{\mu(x_k)}$. For a set $O$ of these operators, $\mathrm{RGX}^O$ is the set of spanner representations built from RGX by the operators of $O$, each $\rho$ defining a spanner $[\![\rho]\!]$. Core spanner representations are $\mathrm{RGX}^{\{\pi, \zeta^{=}, \cup, \bowtie\}}$; regular spanners are those definable in $\mathrm{RGX}^{\{\pi, \cup, \bowtie\}}$.

**Static analysis problems.** For core spanner representations $\rho, \rho_1, \rho_2$: universality asks whether $[\![\rho]\!] = \Upsilon_{\mathsf{SVars}(\rho)}$; equivalence whether $[\![\rho_1]\!] = [\![\rho_2]\!]$; containment whether $[\![\rho_1]\!] \subseteq [\![\rho_2]\!]$; regularity whether $[\![\rho]\!]$ is a regular spanner.

## Depends on

- [Language denoted by a regular expression](../../../../TheoryOfComputation/regular-languages/automata-and-expressions/kleene-s-theorem/is-regex-denoted.md)

## Proof depends on

None.

## Expansion

A regex formula such as $\Sigma^* \cdot x\{a \cdot y\{\Sigma^*\} \cdot (z\{a\} \vee z\{b\})\} \cdot \Sigma^*$ extracts from each word all triples of nested spans of the given shape. String-equality selection is what lifts core spanners beyond regular languages: $\zeta^{=}_{x,y}\, x\{\Sigma^*\} y\{\Sigma^*\}$ recognizes the copy language $\{ww \mid w \in \Sigma^*\}$. Join compares spans, selection compares the strings they cover.

## Sources

- Dominik D. Freydenberger and Mario Holldack, "Document spanners: from expressive power to decision problems", *Theory of Computing Systems* 62(4), 854–898, 2018, <https://doi.org/10.1007/s00224-017-9770-0>; read as the open-access publisher version, <https://link.springer.com/content/pdf/10.1007/s00224-017-9770-0.pdf>: Definitions 2.6–2.15 (spans, spanners, regex formulas, functionality, operators, spanner algebras and core spanners) and the list of static analysis problems in Section 4.2.
