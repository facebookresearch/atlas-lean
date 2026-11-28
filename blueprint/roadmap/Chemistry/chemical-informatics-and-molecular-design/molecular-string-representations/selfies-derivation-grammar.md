# The SELFIES chain-derivation grammar

The chain layer of SELFIES is a context-free grammar whose nonterminals $\mathbf{X}_i$ record the bond budget of the active attachment site. Each atom symbol of the string selects one production, so a symbol sequence drives the derivation instead of being parsed.

Fix a nonempty finite atom-type universe $\mathcal{A}$ and a constraint function $\nu$, and write $\ell_{\max} = \max_{a \in \mathcal{A}} \nu(a)$. The grammar has nonterminals

$$
V = \{\mathbf{S}, \mathbf{X}_1, \mathbf{X}_2, \dots, \mathbf{X}_{\ell_{\max}}\} ,
$$

terminals $\Sigma$ the SMILES symbols, start symbol $\mathbf{S}$, and the convention $\mathbf{X}_0 = \varepsilon$. A SELFIES atom symbol is $[\beta\alpha]$ with bond part $\beta \in \{\varepsilon, =, \#, /, \backslash\}$ and atom part $\alpha$ naming a type $\mathrm{type}(\alpha)$. Write

$$
d(\beta) = \begin{cases} 1, & \beta \in \{\varepsilon, /, \backslash\} \\ 2, & \beta = \texttt{=} \\ 3, & \beta = \texttt{\#} \end{cases}
\qquad
\tilde{\alpha} = \begin{cases} \alpha, & \alpha \in \mathcal{O} \\ [\alpha], & \text{otherwise,} \end{cases}
$$

with $\mathcal{O} = \{\mathrm{B}, \mathrm{C}, \mathrm{N}, \mathrm{O}, \mathrm{S}, \mathrm{P}, \mathrm{F}, \mathrm{Cl}, \mathrm{Br}, \mathrm{I}\}$ the SMILES organic subset, and let $\beta_{\downarrow}(n)$ denote $\beta$ demoted to order $n \le d(\beta)$: $\beta$ itself when $n = d(\beta)$, $\varepsilon$ when $n = 1 \neq d(\beta)$, and $\texttt{=}$ when $n = 2 \neq d(\beta)$. With $\ell = \nu(\mathrm{type}(\alpha))$ and $d_0 = \min(\ell, i, d(\beta))$, the symbol $[\beta\alpha]$ selects

$$
\mathbf{S} \to \tilde{\alpha}\,\mathbf{X}_{\ell} ,
\qquad
\mathbf{X}_i \to \begin{cases} \beta_{\downarrow}(d_0)\,\tilde{\alpha}\,\mathbf{X}_{\ell - d_0}, & \ell > 0 \\ \varepsilon, & \ell = 0 \end{cases}
\qquad (1 \le i \le \ell_{\max}) .
$$

At the start symbol an atom of valence zero is still emitted, as $\mathbf{S} \to \tilde{\alpha}\mathbf{X}_0 = \tilde{\alpha}$; at $\mathbf{X}_i$ with $i \ge 1$ a symbol whose type has $\nu = 0$ emits nothing and ends the derivation. Derivation treats the string as a queue: the head symbol is popped and, with the unique nonterminal of the current string, selects the production; the derivation stops when the queue empties or no nonterminal remains, and the SMILES string is read off by deleting nonterminals. Because each production in the display replaces one nonterminal by at most one, the current string carries at most one nonterminal and the applied production is never ambiguous.

The index $i$ of $\mathbf{X}_i$ is the bond budget of the *active attachment site*, which is the last emitted atom only while no branch is open. The branch and ring symbols of this chapter are not productions of this grammar: they consume arguments, recurse, and restore the parent state, and a queued ring closure can later consume budget at an atom already derived. The later library grammar stated here and the supplementary grammar of the 2020 paper are different production systems for the same idea.

## Depends on

- [Molecular graphs under valence constraints](molecular-graphs-under-valence-constraints.md)
- [Context-free languages](../../../TheoryOfComputation/context-free-languages/grammars-and-pushdown-automata/context-free-languages.md)

## Proof depends on

None.

## Expansion

A formal development gives the symbol alphabet, the map from a symbol and a nonterminal to a production, and the queue-driven step relation over the ordinary context-free derivation relation. The single-nonterminal invariant is an induction on steps, and termination holds because each step pops one symbol of a finite queue. Extending the relation to branch and ring symbols needs the branch transition (reserve $d_0 = \min(i-1, d(\beta))$, consume at most $N$ symbols, resume the parent in $\mathbf{X}_{i - d_0}$) and the deferred ring queue, both given on their own pages.

## Context

Undergraduate to graduate. The chain layer of the SELFIES grammar in the library's streamlined form; the robustness statement of this chapter is about the full decoder, of which this layer is one part.

## Sources

- Alston Lo, Robert Pollice, AkshatKumar Nigam, Andrew D. White, Mario Krenn and Alán Aspuru-Guzik, *Recent advances in the Self-Referencing Embedded Strings (SELFIES) library*, Digital Discovery 2 (2023) 897–908, Section III B–C, Eqs. 8–13. DOI [10.1039/d3dd00044c](https://doi.org/10.1039/d3dd00044c), PMC10408573.
- Mario Krenn, Florian Häse, AkshatKumar Nigam, Pascal Friederich and Alán Aspuru-Guzik, *Self-referencing embedded strings (SELFIES): A 100% robust molecular string representation*, Machine Learning: Science and Technology 1 (2020) 045024, Figure 2, whose rule table is an earlier and different production system. DOI [10.1088/2632-2153/aba947](https://doi.org/10.1088/2632-2153/aba947), arXiv:[1905.13741v2](https://arxiv.org/abs/1905.13741v2).
