# LL(1) lookahead and correct parse tables

Let $G$ be a context-free grammar with start symbol $S$ and productions $X \to \gamma$, with the relations $\mathrm{NULLABLE}$, $\mathrm{FIRST}$ and $\mathrm{FOLLOW}$ of [NULLABLE, FIRST, FOLLOW and LL(1) tables](nullable-first-follow-and-ll-1-tables.md), where $\mathrm{EOF} \in \mathrm{FOLLOW}(S)$. A lookahead symbol $l \in T \cup \{\mathrm{EOF}\}$ is in $\mathrm{LOOKAHEAD}(X \to \gamma)$ if $l \in \mathrm{FIRST}(\gamma)$, or $\gamma$ is nullable and $l \in \mathrm{FOLLOW}(X)$.

Each production carries a semantic action, $X \to \gamma\ \{f\}$, which maps the tuple of semantic values of $\gamma$ to a value for $X$. An *LL(1) parse table* is a finite map from pairs $(X, l)$ of a nonterminal and a lookahead symbol to productions with their actions. It is *correct* for $G$ if, for every nonterminal $X$, lookahead symbol $l$ and production $p$ with its action, the table maps $(X, l)$ to $p$ exactly when $p$ is a production of $G$, the left-hand side of $p$ is $X$, and $l \in \mathrm{LOOKAHEAD}(p)$; so the table contains all and only these lookahead facts. Quantifying over arbitrary stored productions matters: for the grammar $S \to a\,A$, $A \to b$, a test only of entries $(X, l) \mapsto X \to \gamma$ would also accept the stray entry $(S, b) \mapsto A \to b$. A grammar is *LL(1)* if it has a correct parse table, that is, if no lookahead symbol lies in the lookahead sets of two distinct productions with the same left-hand side. The action must be stored: the grammars with the single production $S \to a$ and actions returning $0$ and $1$ would otherwise have the same table but require different results.

The *LL(1) derivation relation* $s \xrightarrow{v} w \mid r$, read "$s$ derives $w$, producing the semantic value $v$ and leaving $r$ unparsed", is defined together with the analogous relation $\gamma \xRightarrow{vs} w \mid r$ for lists of symbols, producing a tuple $vs$ of values:
- a terminal $a$ derives a token $(a, v)$, producing $v$: $a \xrightarrow{v} (a, v) \mid r$;
- the empty list derives the empty word, producing the empty tuple: $[\,] \xRightarrow{()} \varepsilon \mid r$;
- if $s \xrightarrow{v} w \mid w' \cdot r$ and $\gamma \xRightarrow{vs} w' \mid r$, then $s :: \gamma \xRightarrow{(v, vs)} w \cdot w' \mid r$;
- if $X \to \gamma\ \{f\}$ is a production, $\mathrm{peek}(w \cdot r) \in \mathrm{LOOKAHEAD}(X \to \gamma)$ and $\gamma \xRightarrow{vs} w \mid r$, then $X \xrightarrow{f(vs)} w \mid r$;

where $\mathrm{peek}$ returns the terminal $a$ of the first token $(a, v)$ of its argument, or $\mathrm{EOF}$ when the argument is empty.

## Depends on

- [NULLABLE, FIRST, FOLLOW and LL(1) tables](nullable-first-follow-and-ll-1-tables.md)
- [Parsers and recognizers](parsers-and-recognizers.md)

## Sources

- S. Lasser, C. Casinghino, K. Fisher and C. Roux, "A verified LL(1) parser generator", *10th International Conference on Interactive Theorem Proving (ITP 2019)*, LIPIcs 141, 2019, 24:1–24:18, <https://drops.dagstuhl.de/storage/00lipics/lipics-vol141-itp2019/LIPIcs.ITP.2019.24/LIPIcs.ITP.2019.24.pdf>, Section 2: grammars with semantic actions (2.1), the derivation relations of Figure 1 (2.2), the NULLABLE, FIRST, FOLLOW and LOOKAHEAD relations of Figures 2–5 (2.3), and correct LL(1) parse tables and LL(1) grammars (2.4); Section 3.5, the remark that the verified table stores an entire production and its semantic action in each cell.
